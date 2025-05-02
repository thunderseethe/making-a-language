use std::collections::BTreeSet;

use crate::ast::{Ast, ItemWrapper, TypedVar};
use crate::ty::{ClosedRow, Row, RowCombination, RowUniVar, RowVar, Type, TypeUniVar, TypeVar};
use crate::{Evidence, TypeInference};

#[derive(Debug)]
pub struct SubstOut<T> {
  pub unbound_tys: BTreeSet<TypeVar>,
  pub unbound_rows: BTreeSet<RowVar>,
  pub value: T,
}

impl<T> SubstOut<T> {
  pub(super) fn new(value: T) -> Self {
    Self {
      unbound_tys: BTreeSet::default(),
      unbound_rows: BTreeSet::default(),
      value,
    }
  }

  fn with_unbound_ty(mut self, ty_var: TypeVar) -> Self {
    self.unbound_tys.insert(ty_var);
    self
  }

  fn with_unbound_row(mut self, row_var: RowVar) -> Self {
    self.unbound_rows.insert(row_var);
    self
  }

  pub(super) fn merge<U, O>(
    mut self,
    other: SubstOut<U>,
    merge_values: impl FnOnce(T, U) -> O,
  ) -> SubstOut<O> {
    self.unbound_tys.extend(other.unbound_tys);
    self.unbound_rows.extend(other.unbound_rows);
    SubstOut {
      unbound_rows: self.unbound_rows,
      unbound_tys: self.unbound_tys,
      value: merge_values(self.value, other.value),
    }
  }

  pub(crate) fn map<U>(self, f: impl FnOnce(T) -> U) -> SubstOut<U> {
    SubstOut {
      value: f(self.value),
      unbound_tys: self.unbound_tys,
      unbound_rows: self.unbound_rows,
    }
  }
}

impl TypeInference {
  fn substitute_closedrow(&mut self, row: ClosedRow) -> SubstOut<ClosedRow> {
    let mut row_out = SubstOut::new(());
    let values = row
      .values
      .into_iter()
      .map(|ty| {
        let out = self.substitute_ty(ty);
        row_out.unbound_rows.extend(out.unbound_rows);
        row_out.unbound_tys.extend(out.unbound_tys);
        out.value
      })
      .collect();
    row_out.map(|_| ClosedRow {
      fields: row.fields,
      values,
    })
  }

  fn substitute_row(&mut self, row: Row) -> SubstOut<Row> {
    match row {
      Row::Unifier(var) => {
        let root = self.row_unification_table.find(var);
        match self.row_unification_table.probe_value(root) {
          Some(Row::Unifier(_)) => panic!("Unexpected open row found as value of row unification table. This variable should've been `unify_var_var()`, not `unify_var_value()`"),
          Some(Row::Open(v)) => SubstOut::new(Row::Open(v)),
          Some(Row::Closed(row)) => self.substitute_closedrow(row).map(Row::Closed),
          None => {
              let rowvar = self.rowvar_for_unifier(root);
              SubstOut::new(Row::Open(rowvar)).with_unbound_row(rowvar)
          },
        }
      }
      Row::Open(v) => SubstOut::new(Row::Open(v)),
      Row::Closed(row) => self.substitute_closedrow(row).map(Row::Closed),
    }
  }

  fn tyvar_for_unifier(&mut self, var: TypeUniVar) -> TypeVar {
    *self.subst_unifiers_to_tyvars.entry(var).or_insert_with(|| {
      let next = self.next_tyvar;
      self.next_tyvar += 1;
      TypeVar(next)
    })
  }

  fn rowvar_for_unifier(&mut self, var: RowUniVar) -> RowVar {
    *self
      .subst_unifiers_to_rowvars
      .entry(var)
      .or_insert_with(|| {
        let next = self.next_rowvar;
        self.next_rowvar += 1;
        RowVar(next)
      })
  }

  pub(crate) fn substitute_ty(&mut self, ty: Type) -> SubstOut<Type> {
    match ty {
      Type::Int => SubstOut::new(Type::Int),
      Type::Var(v) => SubstOut::new(Type::Var(v)),
      Type::Unifier(v) => {
        let root = self.unification_table.find(v);
        match self.unification_table.probe_value(root) {
          Some(ty) => self.substitute_ty(ty),
          None => {
            let tyvar = self.tyvar_for_unifier(root);
            SubstOut::new(Type::Var(tyvar)).with_unbound_ty(tyvar)
          }
        }
      }
      Type::Fun(arg, ret) => {
        let arg_out = self.substitute_ty(*arg);
        let ret_out = self.substitute_ty(*ret);
        arg_out.merge(ret_out, Type::fun)
      }
      Type::Label(field, value) => self.substitute_ty(*value).map(|ty| Type::label(field, ty)),
      Type::Prod(row) => self.substitute_row(row).map(Type::Prod),
      Type::Sum(row) => self.substitute_row(row).map(Type::Sum),
    }
  }

  pub(crate) fn substitute_ast(&mut self, ast: Ast<TypedVar>) -> SubstOut<Ast<TypedVar>> { 
    match ast {
      Ast::Var(id, v) => self
        .substitute_ty(v.1)
        .map(|ty| Ast::Var(id, TypedVar(v.0, ty))),
      Ast::Int(id, i) => SubstOut::new(Ast::Int(id, i)),
      Ast::Fun(id, arg, body) => self
        .substitute_ty(arg.1)
        .map(|ty| TypedVar(arg.0, ty))
        .merge(self.substitute_ast(*body), |arg, body| {
          Ast::fun(id, arg, body)
        }),
      Ast::App(id, fun, arg) => self
        .substitute_ast(*fun)
        .merge(self.substitute_ast(*arg), |fun, arg| Ast::app(id, fun, arg)),
      // Label constructor and destructor
      Ast::Label(id, label, ast) => self
        .substitute_ast(*ast)
        .map(|ast| Ast::label(id, label, ast)),
      Ast::Unlabel(id, ast, label) => self
        .substitute_ast(*ast)
        .map(|ast| Ast::unlabel(id, ast, label)),
      // Products constructor and destructor
      Ast::Concat(id, left, right) => self
        .substitute_ast(*left)
        .merge(self.substitute_ast(*right), |left, right| {
          Ast::concat(id, left, right)
        }),
      Ast::Project(id, dir, ast) => self
        .substitute_ast(*ast)
        .map(|ast| Ast::project(id, dir, ast)),
      // Sums constructor and destructor
      Ast::Branch(id, left, right) => self
        .substitute_ast(*left)
        .merge(self.substitute_ast(*right), |left, right| {
          Ast::branch(id, left, right)
        }),
      Ast::Inject(id, dir, ast) => self
        .substitute_ast(*ast)
        .map(|ast| Ast::inject(id, dir, ast)),
      Ast::Item(id, item) => SubstOut::new(Ast::Item(id, item)),
    }
  }

  pub(crate) fn substitute_wrapper(
    &mut self,
    wrapper: ItemWrapper,
  ) -> SubstOut<ItemWrapper> {
    fn transpose<T>(vec: Vec<SubstOut<T>>) -> SubstOut<Vec<T>> {
      let mut subst = SubstOut::new(vec![]);
      for ele in vec {
        subst.unbound_tys.extend(ele.unbound_tys);
        subst.unbound_rows.extend(ele.unbound_rows);
        subst.value.push(ele.value);
      }
      subst
    }

    transpose(
      wrapper
        .types
        .into_iter()
        .map(|ty| self.substitute_ty(ty))
        .collect(),
    )
    .merge(
      transpose(
        wrapper
          .rows
          .into_iter()
          .map(|row| self.substitute_row(row))
          .collect(),
      ),
      |t, r| (t, r),
    )
    .merge(
      transpose(
        wrapper
          .evidence
          .into_iter()
          .map(|ev| self.substitute_evidence(ev))
          .collect(),
      ),
      |(types, rows), evidence| {
        ItemWrapper {
          types,
          rows,
          evidence,
        }
      },
    )
  }

  pub(crate) fn substitute_evidence(&mut self, ev: Evidence) -> SubstOut<Evidence> {
    match ev {
      Evidence::RowEquation { left, right, goal } => self
        .substitute_row(left)
        .merge(self.substitute_row(right), |l, r| (l, r))
        .merge(self.substitute_row(goal), |(left, right), goal| {
          Evidence::RowEquation { left, right, goal }
        }),
    }
  }

  pub(crate) fn substitute_row_comb(&mut self, comb: RowCombination) -> SubstOut<Evidence> {
    self
      .substitute_row(comb.left)
      .merge(self.substitute_row(comb.right), |l, r| (l, r))
      .merge(self.substitute_row(comb.goal), |(left, right), goal| {
        Evidence::RowEquation { left, right, goal }
      })
  }
}
