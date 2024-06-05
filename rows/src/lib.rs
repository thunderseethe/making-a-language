#![allow(dead_code)]
use std::collections::{
  BTreeSet, HashSet,
};

use ena::unify::InPlaceUnificationTable;

use self::ast::{
  Ast, TypedVar, Var,
};
use self::subst::SubstOut;
use self::ty::{
  Row, RowCombination,
  RowVar, Type, TypeVar,
};
use self::unification::TypeError;

mod ast;
mod infer;
mod subst;
mod ty;
mod unification;

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
pub enum Constraint {
  TypeEqual(Type, Type),
  RowCombine(RowCombination),
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
pub struct TypeInference {
  unification_table:
    InPlaceUnificationTable<
      TypeVar,
    >,
  row_unification_table:
    InPlaceUnificationTable<
      RowVar,
    >,
  partial_row_combs:
    BTreeSet<RowCombination>,
}

#[derive(
  Debug, Clone, PartialEq, Eq,
)]
enum Evidence {
  RowEquation {
    left: Row,
    right: Row,
    goal: Row,
  },
}

#[derive(
  PartialEq, Eq, Clone, Debug,
)]
struct TypeScheme {
  unbound_rows:
    HashSet<RowVar>,
  unbound_tys:
    HashSet<TypeVar>,
  evidence: Vec<Evidence>,
  ty: Type,
}

fn type_infer(
  ast: Ast<Var>,
) -> Result<
  (Ast<TypedVar>, TypeScheme),
  TypeError,
> {
  let mut ctx = TypeInference {
    unification_table: InPlaceUnificationTable::default(),
    row_unification_table: InPlaceUnificationTable::default(),
    partial_row_combs: BTreeSet::default(),
  };

  // Constraint generation
  let (out, ty) = ctx.infer(
    im::HashMap::default(),
    ast,
  );

  // Constraint solving
  ctx.unification(
    out.constraints,
  )?;

  // Apply our substition to our inferred types
  let subst_out = ctx
    .substitute_ty(ty)
    .merge(
      ctx.substitute_ast(
        out.typed_ast,
      ),
      |ty, ast| (ty, ast),
    );

  let mut ev_out =
    SubstOut::new(());
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

  let subst_out = subst_out
    .merge(ev_out, |l, _| l);
  // Return our typed ast and it's type scheme
  Ok((
    subst_out.value.1,
    TypeScheme {
      unbound_rows: subst_out
        .unbound_rows,
      unbound_tys: subst_out
        .unbound_tys,
      evidence,
      ty: subst_out.value.0,
    },
  ))
}

#[cfg(test)]
mod tests {

  use crate::ast::Direction;
  use crate::ty::ClosedRow;

  use super::*;

  macro_rules! set {
        () => {{ HashSet::new() }};
        ($($ele:expr),*) => {{
            let mut tmp = HashSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

  #[test]
  fn infers_int() {
    let ast = Ast::Int(3);

    let ty_chk = type_infer(ast).expect("Type inference to succeed");
    assert_eq!(
      ty_chk.0,
      Ast::Int(3)
    );
    assert_eq!(
      ty_chk.1.ty,
      Type::Int
    );
  }

  #[test]
  fn infers_id_fun() {
    let x = Var(0);
    let ast = Ast::fun(
      x,
      Ast::Var(x),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(0);
    let typed_x = TypedVar(
      x,
      Type::Var(a),
    );
    assert_eq!(
      ty_chk.0,
      Ast::fun(
        typed_x.clone(),
        Ast::Var(typed_x)
      )
    );
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![],
        unbound_tys: set![a],
        evidence: vec![],
        ty: Type::fun(
          Type::Var(a),
          Type::Var(a)
        ),
      }
    )
  }

  #[test]
  fn infers_k_combinator() {
    let x = Var(0);
    let y = Var(1);
    let ast = Ast::fun(
      x,
      Ast::fun(
        y,
        Ast::Var(x),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(0);
    let b = TypeVar(1);
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![],
        unbound_tys: set![
          a, b
        ],
        evidence: vec![],
        ty: Type::fun(
          Type::Var(a),
          Type::fun(
            Type::Var(b),
            Type::Var(a)
          )
        ),
      }
    );
  }

  #[test]
  fn infers_s_combinator() {
    let x = Var(0);
    let y = Var(1);
    let z = Var(2);
    let ast = Ast::fun(
      x,
      Ast::fun(
        y,
        Ast::fun(
          z,
          Ast::app(
            Ast::app(
              Ast::Var(x),
              Ast::Var(z),
            ),
            Ast::app(
              Ast::Var(y),
              Ast::Var(z),
            ),
          ),
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(2);
    let b = TypeVar(3);
    let c = TypeVar(4);
    let x_ty = Type::fun(
      Type::Var(a),
      Type::fun(
        Type::Var(b),
        Type::Var(c),
      ),
    );
    let y_ty = Type::fun(
      Type::Var(a),
      Type::Var(b),
    );
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![],
        unbound_tys: set![
          a, b, c
        ],
        evidence: vec![],
        ty: Type::fun(
          x_ty,
          Type::fun(
            y_ty,
            Type::fun(
              Type::Var(a),
              Type::Var(c)
            )
          )
        ),
      }
    )
  }

  fn single_row(
    field: impl ToString,
    value: Type,
  ) -> ClosedRow {
    ClosedRow {
      fields: vec![
        field.to_string()
      ],
      values: vec![value],
    }
  }

  #[test]
  fn test_wand_combinator() {
    let m = Var(0);
    let n = Var(1);

    let ast = Ast::fun(
      m,
      Ast::fun(
        n,
        Ast::unlabel(
          Ast::project(
            Direction::Left,
            Ast::concat(
              Ast::Var(m),
              Ast::Var(n),
            ),
          ),
          "x",
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let m = RowVar(2);
    let n = RowVar(3);
    let goal = RowVar(0);
    let a = TypeVar(2);
    assert_eq!(
      ty_chk.1,
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
    let f = Var(0);
    let g = Var(1);
    let x = Var(2);
    let ast = Ast::fun(
      f,
      Ast::fun(
        g,
        Ast::fun(
          x,
          Ast::app(
            Ast::branch(Ast::Var(f), Ast::Var(g)),
            Ast::inject(Direction::Right, Ast::label("Con", Ast::Var(x))),
          ),
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let f = RowVar(3);
    let g = RowVar(4);
    let goal = RowVar(2);
    let a = TypeVar(2);
    let r = TypeVar(3);
    assert_eq!(
      ty_chk.1,
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

  #[test]
  fn type_infer_fails() {
    let x = Var(0);
    let ast = Ast::app(
      Ast::fun(
        x,
        Ast::app(
          Ast::Var(x),
          Ast::Int(3),
        ),
      ),
      Ast::Int(1),
    );

    let ty_chk_res =
      type_infer(ast);

    assert_eq!(
      ty_chk_res,
      Err(TypeError::TypeNotEqual((
        Type::fun(Type::Int, Type::Var(TypeVar(1))),
        Type::Int
      )))
    );
  }
}
