use std::collections::HashMap;

use crate::ast::NodeId;
use crate::ty::{Row, RowCombination, RowUniVar, RowVar, Type, TypeUniVar, TypeVar};
use crate::{Constraint, Evidence, TypeScheme};

pub(crate) struct Instantiate<'a> {
  id: NodeId,
  tyvar_to_unifiers: &'a HashMap<TypeVar, TypeUniVar>,
  rowvar_to_unifiers: &'a HashMap<RowVar, RowUniVar>,
}
impl<'a> Instantiate<'a> {
  pub(crate) fn new(
    id: NodeId,
    tyvar_to_unifiers: &'a HashMap<TypeVar, TypeUniVar>,
    rowvar_to_unifiers: &'a HashMap<RowVar, RowUniVar>,
  ) -> Self {
    Self {
      id,
      tyvar_to_unifiers,
      rowvar_to_unifiers,
    }
  }

  pub(crate) fn type_scheme(&self, ty_scheme: TypeScheme) -> (Vec<Constraint>, Type) {
    let constraints = ty_scheme
      .evidence
      .into_iter()
      .map(|ev| self.evidence(ev))
      .collect();
    let ty = self.ty(ty_scheme.ty);
    (constraints, ty)
  }

  fn evidence(&self, ev: Evidence) -> Constraint {
    match ev {
      Evidence::RowEquation { left, right, goal } => Constraint::RowCombine(
        self.id,
        RowCombination {
          left: self.row(left),
          right: self.row(right),
          goal: self.row(goal),
        },
      ),
    }
  }

  fn row(&self, row: Row) -> Row {
    match row {
      // Type Scheme's should have been generalized and only contain Row::Open.
      // If we see a Unifier in a type scheme our type checker has a bug in it.
      Row::Unifier(_) => panic!("Leftover unifier in type scheme"),
      Row::Open(var) => self
        .rowvar_to_unifiers
        .get(&var)
        .copied()
        .map(Row::Unifier)
        .unwrap_or_else(|| {
          panic!(
            "Expected row var {:?} to be mapped to fresh unifier in instantiation",
            var
          )
        }),
      Row::Closed(mut row) => {
        row.values = row.values.into_iter().map(|ty| self.ty(ty)).collect();
        Row::Closed(row)
      }
    }
  }

  fn ty(&self, ty: Type) -> Type {
    match ty {
      Type::Var(var) => self
        .tyvar_to_unifiers
        .get(&var)
        .copied()
        .map(Type::Unifier)
        .unwrap_or_else(|| {
          panic!(
            "Expected type var {:?} to be mapped to fresh unifier in instantiation",
            var
          )
        }),
      ty @ Type::Int | ty @ Type::Unifier(_) => ty,
      Type::Fun(arg, ret) => {
        let arg = self.ty(*arg);
        let ret = self.ty(*ret);
        Type::fun(arg, ret)
      }
      Type::Prod(row) => Type::Prod(self.row(row)),
      Type::Sum(row) => Type::Sum(self.row(row)),
      Type::Label(label, ty) => Type::Label(label, ty),
    }
  }
}
