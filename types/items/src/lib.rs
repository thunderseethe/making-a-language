#![allow(dead_code)]
use std::collections::{BTreeSet, HashMap, HashSet};

use ena::unify::InPlaceUnificationTable;

pub use self::ast::{Ast, Direction, ItemId, TypedVar, Var, NodeId, ItemWrapper};
use self::subst::SubstOut;
pub use self::ty::{ClosedRow, Row, RowCombination, RowVar, Type, TypeVar};
use self::ty::{RowUniVar, TypeUniVar};
use self::unification::{TypeError, TypeErrorKind};

mod ast;
pub mod builder;
mod infer;
mod inst;
mod subst;
mod ty;
mod unification;

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Constraint {
  TypeEqual(NodeId, Type, Type),
  RowCombine(NodeId, RowCombination),
}

/// Responsible for all the metadata our type checker wants about Items.
/// We could imagine this would be produced as the result of parsing and name resolution in a more
/// complete compiler.
/// But for our purposes, we presume something like that has already happened and present the
/// metadata in a format easy to digest for our typechecker.
#[derive(Default, Clone)]
pub struct ItemSource {
  pub types: HashMap<ItemId, TypeScheme>,
}
impl ItemSource {
  fn type_of_item(&self, item_id: ItemId) -> TypeScheme {
    // We make a simplifying assumption here: item_id will always be present in types
    // This is reasonable, even in a real compiler. If during name resolution we produce an
    // ItemId without a corresponding type either:
    // 1) that's an error, we're referring to an undefined item.
    // 2) Our language should infer the type for that item.
    // Our language won't handle case 2) because our items are required to always have
    // signatures. So we're safe to assume this will always succeed.
    self.types[&item_id].clone()
  }
}
impl FromIterator<(ItemId, TypeScheme)> for ItemSource {
  fn from_iter<T: IntoIterator<Item = (ItemId, TypeScheme)>>(iter: T) -> Self {
    Self {
      types: iter.into_iter().collect(),
    }
  }
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
#[derive(Default)]
pub struct TypeInference {
  unification_table: InPlaceUnificationTable<TypeUniVar>,
  row_unification_table: InPlaceUnificationTable<RowUniVar>,
  partial_row_combs: BTreeSet<RowCombination>,
  item_source: ItemSource,

  row_to_ev: HashMap<NodeId, RowCombination>,
  branch_to_ret_ty: HashMap<NodeId, Type>,

  item_wrappers: HashMap<NodeId, ItemWrapper>,
  subst_unifiers_to_tyvars: HashMap<TypeUniVar, TypeVar>,
  next_tyvar: u32,
  subst_unifiers_to_rowvars: HashMap<RowUniVar, RowVar>,
  next_rowvar: u32,
}
impl TypeInference {
  fn normalize_mentioned_row_combs<T>(
    &mut self,
    subst_out: SubstOut<T>,
  ) -> SubstOut<(T, Vec<Evidence>)> {
    let mut subst_out = subst_out.map(|t| (t, vec![]));
    for norm_row_comb in std::mem::take(&mut self.partial_row_combs)
      .into_iter()
      .map(|row_comb| self.substitute_row_comb(row_comb))
    {
      if norm_row_comb
        .unbound_tys
        .intersection(&subst_out.unbound_tys)
        .next()
        .is_some()
        || norm_row_comb
          .unbound_rows
          .intersection(&subst_out.unbound_rows)
          .next()
          .is_some()
      {
        subst_out = subst_out.merge(norm_row_comb, |(t, mut evidences), ev| {
          evidences.push(ev);
          (t, evidences)
        })
      }
    }
    subst_out
  }
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
  pub item_wrappers: HashMap<NodeId, ItemWrapper>,
}

pub fn type_infer_with_items(
  item_source: ItemSource,
  ast: Ast<Var>,
) -> Result<TypesOutput, TypeError> {
  let mut ctx = TypeInference {
    item_source,
    ..Default::default()
  };

  // Constraint generation
  let (out, ty) = ctx.infer(im::HashMap::default(), ast);

  // Constraint solving
  ctx.unification(out.constraints)?;

  // Apply our substition to our inferred types
  let subst_out = ctx
    .substitute_ty(ty)
    .merge(ctx.substitute_ast(out.typed_ast), |ty, ast| (ty, ast));

  let mut evidence_subst = ctx.normalize_mentioned_row_combs(subst_out);
  let row_to_ev = std::mem::take(&mut ctx.row_to_ev)
    .into_iter()
    .map(|(id, combo)| {
      let out = ctx.substitute_row_comb(combo);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();
  let item_wrappers = std::mem::take(&mut ctx.item_wrappers)
    .into_iter()
    .map(|(id, wrapper)| {
      let out = ctx.substitute_wrapper(wrapper);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();
  let branch_to_ret_ty = std::mem::take(&mut ctx.branch_to_ret_ty)
    .into_iter()
    .map(|(id, ty)| {
      let out = ctx.substitute_ty(ty);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();

  // Return our typed ast and it's type scheme
  let ((ty, ast), evidence) = evidence_subst.value;
  Ok(TypesOutput {
    typed_ast: ast,
    scheme: TypeScheme {
      unbound_rows: evidence_subst.unbound_rows,
      unbound_tys: evidence_subst.unbound_tys,
      evidence,
      ty,
    },
    row_to_ev,
    branch_to_ret_ty,
    item_wrappers,
  })
}

pub fn type_infer(ast: Ast<Var>) -> Result<TypesOutput, TypeError> {
  type_infer_with_items(ItemSource::default(), ast)
}

fn type_check_with_items(
  item_source: ItemSource,
  ast: Ast<Var>,
  signature: TypeScheme,
) -> Result<TypesOutput, TypeError> {
  let mut ctx = TypeInference {
    item_source,
    next_tyvar: signature
      .unbound_tys
      .iter()
      .max()
      .map(|tv| tv.0 + 1)
      .unwrap_or(0),
    next_rowvar: signature
      .unbound_rows
      .iter()
      .max()
      .map(|rv| rv.0 + 1)
      .unwrap_or(0),
    ..Default::default()
  };

  let id = ast.id();
  // Constraint generation
  let mut out = ctx.check(im::HashMap::default(), ast, signature.ty.clone());

  // Add any evidence in our type annotation to be used during solving
  out
    .constraints
    .extend(signature.evidence.iter().map(|ev| match ev {
      Evidence::RowEquation { left, right, goal } => Constraint::RowCombine(
        id,
        RowCombination {
          left: left.clone(),
          right: right.clone(),
          goal: goal.clone(),
        },
      ),
    }));

  // Constraint solving
  ctx.unification(out.constraints)?;

  // Apply our substition to our ast
  let subst_out = ctx.substitute_ast(out.typed_ast);

  // Here we have to make sure we didn't invent new constraints or types
  // during unification, and if we did that's an error.
  let mut evidence_subst = ctx.normalize_mentioned_row_combs(subst_out);
  let row_to_ev = std::mem::take(&mut ctx.row_to_ev)
    .into_iter()
    .map(|(id, combo)| {
      let out = ctx.substitute_row_comb(combo);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();
  let item_wrappers = std::mem::take(&mut ctx.item_wrappers)
    .into_iter()
    .map(|(id, wrapper)| {
      let out = ctx.substitute_wrapper(wrapper);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();
  let branch_to_ret_ty = std::mem::take(&mut ctx.branch_to_ret_ty)
    .into_iter()
    .map(|(id, ty)| {
      let out = ctx.substitute_ty(ty);
      evidence_subst.unbound_rows.extend(out.unbound_rows);
      evidence_subst.unbound_tys.extend(out.unbound_tys);
      (id, out.value)
    })
    .collect();
  let (ast, evs) = evidence_subst.value;

  let extra_types = evidence_subst
    .unbound_tys
    .difference(&signature.unbound_tys)
    .copied()
    .collect::<Vec<_>>();
  let extra_row = evidence_subst
    .unbound_rows
    .difference(&signature.unbound_rows)
    .copied()
    .collect::<Vec<_>>();

  let sig_evs = signature.evidence.iter().cloned().collect::<HashSet<_>>();
  let extra_evidence = evs
    .into_iter()
    .collect::<HashSet<_>>()
    .difference(&sig_evs)
    .cloned()
    .collect::<Vec<_>>();
  if !extra_types.is_empty() || !extra_row.is_empty() || !extra_evidence.is_empty() {
    return Err(TypeError {
      kind: TypeErrorKind::CheckIntroducedExtraVariablesOrConstraints {
        extra_types,
        extra_row,
        extra_evidence,
      },
      node_id: id,
    });
  }

  Ok(TypesOutput {
    typed_ast: ast,
    scheme: signature,
    row_to_ev,
    branch_to_ret_ty,
    item_wrappers,
  })
}

fn type_check(ast: Ast<Var>, signature: TypeScheme) -> Result<TypesOutput, TypeError> {
  type_check_with_items(ItemSource::default(), ast, signature)
}

#[cfg(test)]
mod tests {
  use crate::ast::Direction;
  use crate::ty::ClosedRow;

  use self::builder::AstBuilder;

  use super::*;

  use pretty_assertions::assert_eq;

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

    let a = TypeVar(0);
    let b = TypeVar(1);
    let c = TypeVar(2);
    let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
    let y_ty = Type::fun(Type::Var(a), Type::Var(b));
    assert_eq!(
      ty_chk.scheme,
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
        kind: TypeErrorKind::TypeNotEqual((Type::fun(Type::Int, Type::Unifier(TypeUniVar { id: 1 })), Type::Int)),
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

    let m = RowVar(0);
    let n = RowVar(1);
    let goal = RowVar(2);
    let a = TypeVar(0);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_rows: set![n, RowVar(3), m, goal],
        unbound_tys: set![a],
        evidence: vec![
          Evidence::RowEquation {
            left: Row::Open(m),
            right: Row::Open(n),
            goal: Row::Open(goal)
          },
          Evidence::RowEquation {
            left: Row::Closed(single_row("x", Type::Var(a))),
            right: Row::Open(RowVar(3)),
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

    let f = RowVar(0);
    let g = RowVar(1);
    let goal = RowVar(3);
    let a = TypeVar(1);
    let r = TypeVar(0);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound_rows: set![g, f, RowVar(2), goal],
        unbound_tys: set![a, r],
        evidence: vec![
          Evidence::RowEquation {
            left: Row::Open(RowVar(2)),
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
  fn type_check_items() {
    let b = AstBuilder::default();
    let ast = b.make_funs(|[m, n]| {
      b.unlabel(
        b.project(Direction::Left, 
          b.concat(b.var(m), b.var(n))),
        "x",
      )
    });

    let r = RowVar(0);
    let s = RowVar(1);
    let w = RowVar(2);
    let a = TypeVar(0);
    let scheme = TypeScheme {
      unbound_rows: set![r, s, w, RowVar(3)],
      unbound_tys: set![a],
      evidence: vec![
        Evidence::RowEquation {
          left: Row::Open(r),
          right: Row::Open(s),
          goal: Row::Open(w),
        },
        Evidence::RowEquation {
          left: Row::single("x", Type::Var(a)),
          right: Row::Open(RowVar(3)),
          goal: Row::Open(w),
        },
      ],
      ty: Type::fun(
        Type::Prod(Row::Open(r)),
        Type::fun(Type::Prod(Row::Open(s)), Type::Var(a)),
      ),
    };

    let out = type_check(ast, scheme);

    assert!(out.is_ok());
  }

  #[test]
  fn type_check_item_fails() {
    let a = TypeVar(0);

    let b = AstBuilder::default();
    let ast = b.make_funs(|[x, y]| {
      b.app(b.var(y), b.var(x))
    }); 
    let signature = TypeScheme {
      unbound_tys: set![a],
      unbound_rows: set![],
      evidence: vec![],
      ty: Type::fun(
        Type::Var(a),
        Type::fun(Type::fun(Type::Int, Type::Int), Type::Int),
      ),
    };

    let out = type_check(ast, signature);

    assert_eq!(
      out,
      Err(TypeError {
        kind: TypeErrorKind::TypeNotEqual((Type::Var(a), Type::Int)),
        node_id: NodeId(0),
      })
    );
  }

  #[test]
  fn type_infer_partial_wand_item_app() {
    let wand = ItemId(0);

    let b = AstBuilder::default();
    let ast = b.make_funs(|[m]| {
      b.app(
        b.app(b.item(wand), b.var(m)),
        b.label("y", b.int(3))
      )
    });

    let r = RowVar(0);
    let s = RowVar(1);
    let w = RowVar(2);
    let a = TypeVar(0);
    let wand_scheme = TypeScheme {
      unbound_rows: set![r, s, w, RowVar(3)],
      unbound_tys: set![a],
      evidence: vec![
        Evidence::RowEquation {
          left: Row::Open(r),
          right: Row::Open(s),
          goal: Row::Open(w),
        },
        Evidence::RowEquation {
          left: Row::Open(RowVar(3)),
          right: Row::single("x", Type::Var(a)),
          goal: Row::Open(w),
        },
      ],
      ty: Type::fun(
        Type::Prod(Row::Open(r)),
        Type::fun(Type::Prod(Row::Open(s)), Type::Var(a)),
      ),
    };

    let item_source = ItemSource::from_iter([(wand, wand_scheme)]);

    let out =
      type_infer_with_items(item_source, ast).expect("Expected type inference to succeed");

    let y_unused = RowVar(0);
    let goal = RowVar(1);
    let x_unused = RowVar(2);
    assert_eq!(
      out.scheme,
      TypeScheme {
        unbound_rows: set![y_unused, goal, x_unused],
        unbound_tys: set![a],
        evidence: vec![
          Evidence::RowEquation {
            left: Row::Open(y_unused),
            right: Row::single("y", Type::Int),
            goal: Row::Open(goal),
          },
          Evidence::RowEquation {
            left: Row::Open(x_unused),
            right: Row::single("x", Type::Var(a)),
            goal: Row::Open(goal),
          },
        ],
        ty: Type::fun(Type::Prod(Row::Open(r)), Type::Var(a)),
      },
    );
  }
}
