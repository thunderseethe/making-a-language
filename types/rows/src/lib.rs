#![allow(dead_code)]
use std::collections::{BTreeSet, HashMap};

use ena::unify::InPlaceUnificationTable;

pub use self::ast::{Ast, Direction, TypedVar, Var, NodeId};
use self::subst::SubstOut;
pub use self::ty::{ClosedRow, Row, RowCombination, RowVar, Type, TypeVar};
use self::unification::TypeError;

mod ast;
pub mod builder;
mod infer;
mod subst;
mod ty;
mod unification;

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
enum Constraint {
  TypeEqual(NodeId, Type, Type),
  RowCombine(NodeId, RowCombination),
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
#[derive(Default)]
pub struct TypeInference {
  unification_table: InPlaceUnificationTable<TypeVar>,
  row_unification_table: InPlaceUnificationTable<RowVar>,
  partial_row_combs: BTreeSet<RowCombination>,
  row_to_ev: HashMap<NodeId, RowCombination>,
  branch_to_ret_ty: HashMap<NodeId, Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Evidence {
  RowEquation { left: Row, right: Row, goal: Row },
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeScheme {
  pub unbound_rows: BTreeSet<RowVar>,
  pub unbound_tys: BTreeSet<TypeVar>,
  pub evidence: Vec<Evidence>,
  pub ty: Type,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypesOutput {
  pub typed_ast: Ast<TypedVar>,
  pub scheme: TypeScheme,
  pub row_to_ev: HashMap<NodeId, Evidence>,
  pub branch_to_ret_ty: HashMap<NodeId, Type>,
}

pub fn type_infer(ast: Ast<Var>) -> Result<TypesOutput, TypeError> {
  let mut ctx = TypeInference::default();
  // Constraint generation
  let (out, ty) = ctx.infer(im::HashMap::default(), ast);

  // Constraint solving
  ctx.unification(out.constraints)?;

  // Apply our substition to our inferred types
  let subst_out = ctx
    .substitute_ty(ty)
    .merge(ctx.substitute_ast(out.typed_ast), |ty, ast| (ty, ast));

  let mut ev_out = SubstOut::new(());
  let evidence = std::mem::take(&mut ctx.partial_row_combs)
    .into_iter()
    .filter_map(|row_comb| match row_comb {
      RowCombination {
        left: Row::Open(left),
        right,
        goal,
      } if subst_out.unbound_rows.contains(&left) => Some(RowCombination {
        left: Row::Open(left),
        right,
        goal,
      }),
      RowCombination {
        left: Row::Closed(left),
        right,
        goal,
      } if left.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => Some(RowCombination {
        left: Row::Closed(left),
        right,
        goal,
      }),
      RowCombination {
        left,
        right: Row::Open(right),
        goal,
      } if subst_out.unbound_rows.contains(&right) => Some(RowCombination {
        left,
        right: Row::Open(right),
        goal,
      }),
      RowCombination {
        left,
        right: Row::Closed(right),
        goal,
      } if right.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => {
        Some(RowCombination {
          left,
          right: Row::Closed(right),
          goal,
        })
      }
      RowCombination {
        left,
        right,
        goal: Row::Open(goal),
        ..
      } if subst_out.unbound_rows.contains(&goal) => Some(RowCombination {
        left,
        right,
        goal: Row::Open(goal),
      }),
      RowCombination {
        left,
        right,
        goal: Row::Closed(goal),
      } if goal.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => Some(RowCombination {
        left,
        right,
        goal: Row::Closed(goal),
      }),
      _ => None,
    })
    .map(|comb| {
      let out = ctx.substitute_row_comb(comb);
      ev_out.unbound_rows.extend(out.unbound_rows);
      ev_out.unbound_tys.extend(out.unbound_tys);
      out.value
    })
    .collect();

  let row_to_ev = std::mem::take(&mut ctx.row_to_ev).into_iter()
        .map(|(id, combo)| {
          let out = ctx.substitute_row_comb(combo);
          ev_out.unbound_rows.extend(out.unbound_rows);
          ev_out.unbound_tys.extend(out.unbound_tys);
          (id, out.value)
        })
        .collect();
  let branch_to_ret_ty = std::mem::take(&mut ctx.branch_to_ret_ty).into_iter()
      .map(|(id, ty)| {
        let out = ctx.substitute_ty(ty);
        ev_out.unbound_rows.extend(out.unbound_rows);
        ev_out.unbound_tys.extend(out.unbound_tys);
        (id, out.value)
      })
      .collect();
  let subst_out = subst_out.merge(ev_out, |l, _| l);
  // Return our typed ast and it's type scheme
  Ok(TypesOutput {
    typed_ast: subst_out.value.1,
    scheme: TypeScheme {
      unbound_rows: subst_out.unbound_rows,
      unbound_tys: subst_out.unbound_tys,
      evidence,
      ty: subst_out.value.0,
    },
    row_to_ev,
    branch_to_ret_ty
  })
}

#[cfg(test)]
mod tests {
  use crate::ast::Direction;
  use crate::ty::ClosedRow;

  use self::builder::AstBuilder;
  use self::unification::{TypeError, TypeErrorKind};

  use super::*;

  macro_rules! set {
        () => {{ BTreeSet::new() }};
        ($($ele:expr),*) => {{
            let mut tmp = BTreeSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

  #[test]
  fn infers_int() {
    let b = AstBuilder::default();
    let ast = b.int(3);

    let ty_chk = type_infer(ast).expect("Type inference to succeed");
    assert_eq!(ty_chk.typed_ast, Ast::Int(NodeId(0), 3));
    assert_eq!(ty_chk.scheme.ty, Type::Int);
  }

  #[test]
  fn infers_id_fun() {
    let x = Var(0);
    let b = AstBuilder::default();
    let ast = b.fun(x, b.var(x));

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(0);
    let typed_x = TypedVar(x, Type::Var(a));
    assert_eq!(
      ty_chk.typed_ast,
      Ast::fun(NodeId(1), typed_x.clone(), Ast::Var(NodeId(0), typed_x))
    );
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_tys: set![a],
        unbound_rows: set![],
        evidence: vec![],
        ty: Type::fun(Type::Var(a), Type::Var(a)),
      }
    )
  }

  #[test]
  fn infers_k_combinator() {
    let x = Var(0);
    let y = Var(1);
    let b = AstBuilder::default();
    let ast = b.funs([x, y], b.var(x));

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(0);
    let b = TypeVar(1);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_tys: set![a, b],
        unbound_rows: set![],
        evidence: vec![],
        ty: Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(a))),
      }
    );
  }

  #[test]
  fn infers_s_combinator() {
    let x = Var(0);
    let y = Var(1);
    let z = Var(2);
    let b = AstBuilder::default();
    let ast = b.funs(
      [x, y, z],
      b.app(b.app(b.var(x), b.var(z)), b.app(b.var(y), b.var(z))),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(2);
    let b = TypeVar(3);
    let c = TypeVar(4);
    let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
    let y_ty = Type::fun(Type::Var(a), Type::Var(b));
    assert_eq!(
      ty_chk.scheme ,
      TypeScheme {
        unbound_tys: set![a, b, c],
        unbound_rows: set![],
        evidence: vec![],
        ty: Type::fun(x_ty, Type::fun(y_ty, Type::fun(Type::Var(a), Type::Var(c)))),
      }
    )
  }

  #[test]
  fn type_infer_fails() {
    let x = Var(0);
    let b = AstBuilder::default();
    let ast = b.locals([(x, b.int(1))], b.app(b.var(x), b.int(3)));

    let ty_chk_res = type_infer(ast);

    assert_eq!(
      ty_chk_res,
      Err(TypeError {
        kind: TypeErrorKind::TypeNotEqual((Type::fun(Type::Int, Type::Var(TypeVar(1))), Type::Int)),
        node_id: NodeId(1)
      })
    );
  }

  fn single_row(field: impl ToString, value: Type) -> ClosedRow {
    ClosedRow {
      fields: vec![field.to_string()],
      values: vec![value],
    }
  }

  #[test]
  fn test_wand_combinator() {
    let b = AstBuilder::default();
    let ast = b.make_funs(|[m, n]| {
      b.unlabel(
        b.project(Direction::Left, b.concat(b.var(m), b.var(n))),
        "x",
      )
    });

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let m = RowVar(2);
    let n = RowVar(3);
    let goal = RowVar(0);
    let a = TypeVar(2);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_rows: set![n, RowVar(1), m, goal],
        unbound_tys: set![a],
        evidence: vec![
          Evidence::RowEquation {
            left: Row::Open(m),
            right: Row::Open(n),
            goal: Row::Open(goal)
          },
          Evidence::RowEquation {
            left: Row::Closed(single_row("x", Type::Var(a))),
            right: Row::Open(RowVar(1)),
            goal: Row::Open(goal)
          }
        ],
        ty: Type::fun(
          Type::Prod(Row::Open(m)),
          Type::fun(Type::Prod(Row::Open(n)), Type::Var(a))
        )
      }
    );
  }

  #[test]
  fn test_sums() {
    let b = AstBuilder::default();
    let ast = b.make_funs(|[f, g, x]| {
      b.app(
        b.branch(b.var(f), b.var(g)),
        b.inject(Direction::Right, b.label("Con", b.var(x))),
      )
    });
    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let f = RowVar(3);
    let g = RowVar(4);
    let goal = RowVar(2);
    let a = TypeVar(2);
    let r = TypeVar(3);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_rows: set![g, f, RowVar(0), goal],
        unbound_tys: set![a, r],
        evidence: vec![
          Evidence::RowEquation {
            left: Row::Open(RowVar(0)),
            right: Row::Closed(single_row("Con", Type::Var(a))),
            goal: Row::Open(goal)
          },
          Evidence::RowEquation {
            left: Row::Open(f),
            right: Row::Open(g),
            goal: Row::Open(goal)
          }
        ],
        ty: Type::fun(
          Type::fun(Type::Sum(Row::Open(f)), Type::Var(r)),
          Type::fun(
            Type::fun(Type::Sum(Row::Open(g)), Type::Var(r)),
            Type::fun(Type::Var(a), Type::Var(r))
          )
        ),
      }
    );
  }

}
