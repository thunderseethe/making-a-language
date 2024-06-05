use std::collections::HashSet;

use crate::ast::{
  Ast, TypedVar,
};
use crate::ty::{
  ClosedRow, Row,
  RowCombination, RowVar,
  Type, TypeVar,
};
use crate::{
  Evidence, TypeInference,
};

pub struct SubstOut<T> {
  pub unbound_tys:
    HashSet<TypeVar>,
  pub unbound_rows:
    HashSet<RowVar>,
  pub value: T,
}

impl<T> SubstOut<T> {
  pub(super) fn new(
    value: T,
  ) -> Self {
    Self {
      unbound_tys:
        HashSet::default(),
      unbound_rows:
        HashSet::default(),
      value,
    }
  }

  fn insert_unbound_ty(
    &mut self,
    ty_var: TypeVar,
  ) {
    self
      .unbound_tys
      .insert(ty_var);
  }
  fn with_unbound_ty(
    mut self,
    ty_var: TypeVar,
  ) -> Self {
    self.insert_unbound_ty(
      ty_var,
    );
    self
  }

  fn with_unbound_row(
    mut self,
    row_var: RowVar,
  ) -> Self {
    self
      .unbound_rows
      .insert(row_var);
    self
  }

  pub(super) fn merge<
    U,
    O,
  >(
    mut self,
    other: SubstOut<U>,
    merge_values: impl FnOnce(
      T,
      U,
    )
      -> O,
  ) -> SubstOut<O> {
    self.unbound_tys.extend(
      other.unbound_tys,
    );
    self.unbound_rows.extend(
      other.unbound_rows,
    );
    SubstOut {
      unbound_rows: self
        .unbound_rows,
      unbound_tys: self
        .unbound_tys,
      value: merge_values(
        self.value,
        other.value,
      ),
    }
  }

  fn map<U>(
    self,
    f: impl FnOnce(T) -> U,
  ) -> SubstOut<U> {
    SubstOut {
      value: f(self.value),
      unbound_tys: self
        .unbound_tys,
      unbound_rows: self
        .unbound_rows,
    }
  }
}

impl TypeInference {
  fn substitute_closedrow(
    &mut self,
    row: ClosedRow,
  ) -> SubstOut<ClosedRow> {
    let mut row_out =
      SubstOut::new(());
    let values = row
      .values
      .into_iter()
      .map(|ty| {
        let out = self
          .substitute_ty(ty);
        row_out
          .unbound_rows
          .extend(
            out.unbound_rows,
          );
        row_out
          .unbound_tys
          .extend(
            out.unbound_tys,
          );
        out.value
      })
      .collect();
    row_out.map(|_| {
      ClosedRow {
        fields: row.fields,
        values,
      }
    })
  }

  fn substitute_row(
    &mut self,
    row: Row,
  ) -> SubstOut<Row> {
    match row {
    Row::Open(var) => {
      let root = self.row_unification_table.find(var);
      match self.row_unification_table.probe_value(root) {
        Some(row) => self.substitute_closedrow(row).map(Row::Closed),
        None => SubstOut::new(Row::Open(root)).with_unbound_row(root),
      }
    }
    Row::Closed(row) => self.substitute_closedrow(row).map(Row::Closed),
  }
  }

  pub(crate) fn substitute_ty(
    &mut self,
    ty: Type,
  ) -> SubstOut<Type> {
    match ty {
      Type::Int => {
        SubstOut::new(
          Type::Int,
        )
      }
      Type::Var(v) => {
        let root = self
          .unification_table
          .find(v);
        match self
          .unification_table
          .probe_value(root)
        {
          Some(ty) => self
            .substitute_ty(
              ty,
            ),
          None => {
            SubstOut::new(
              Type::Var(root),
            )
            .with_unbound_ty(
              root,
            )
          }
        }
      }
      Type::Fun(arg, ret) => {
        let arg_out = self
          .substitute_ty(
            *arg,
          );
        let ret_out = self
          .substitute_ty(
            *ret,
          );
        arg_out.merge(
          ret_out,
          Type::fun,
        )
      }
      Type::Label(
        field,
        value,
      ) => self
        .substitute_ty(*value)
        .map(|ty| {
          Type::label(
            field, ty,
          )
        }),
      Type::Prod(row) => self
        .substitute_row(row)
        .map(Type::Prod),
      Type::Sum(row) => self
        .substitute_row(row)
        .map(Type::Sum),
    }
  }

  pub(crate) fn substitute_ast(
    &mut self,
    ast: Ast<TypedVar>,
  ) -> SubstOut<Ast<TypedVar>>
  {
    match ast {
      Ast::Var(v) => self
        .substitute_ty(v.1)
        .map(|ty| {
          Ast::Var(TypedVar(
            v.0, ty,
          ))
        }),
      Ast::Int(i) => {
        SubstOut::new(
          Ast::Int(i),
        )
      }
      Ast::Fun(arg, body) => {
        self
          .substitute_ty(
            arg.1,
          )
          .map(|ty| {
            TypedVar(
              arg.0, ty,
            )
          })
          .merge(
            self
              .substitute_ast(
                *body,
              ),
            Ast::fun,
          )
      }
      Ast::App(fun, arg) => {
        self
          .substitute_ast(
            *fun,
          )
          .merge(
            self
              .substitute_ast(
                *arg,
              ),
            Ast::app,
          )
      }
      // Label constructor and destructor
      Ast::Label(
        label,
        ast,
      ) => self
        .substitute_ast(*ast)
        .map(|ast| {
          Ast::label(
            label, ast,
          )
        }),
      Ast::Unlabel(
        ast,
        label,
      ) => self
        .substitute_ast(*ast)
        .map(|ast| {
          Ast::unlabel(
            ast, label,
          )
        }),
      // Products constructor and destructor
      Ast::Concat(
        left,
        right,
      ) => self
        .substitute_ast(*left)
        .merge(
          self
            .substitute_ast(
              *right,
            ),
          Ast::concat,
        ),
      Ast::Project(
        dir,
        ast,
      ) => self
        .substitute_ast(*ast)
        .map(|ast| {
          Ast::project(
            dir, ast,
          )
        }),
      // Sums constructor and destructor
      Ast::Branch(
        left,
        right,
      ) => self
        .substitute_ast(*left)
        .merge(
          self
            .substitute_ast(
              *right,
            ),
          Ast::branch,
        ),
      Ast::Inject(
        dir,
        ast,
      ) => self
        .substitute_ast(*ast)
        .map(|ast| {
          Ast::inject(
            dir, ast,
          )
        }),
    }
  }

  pub(crate) fn substitute_row_comb(
    &mut self,
    comb: RowCombination,
  ) -> SubstOut<Evidence> {
    self
    .substitute_row(comb.left)
    .merge(self.substitute_row(comb.right), |l, r| (l, r))
    .merge(self.substitute_row(comb.goal), |(left, right), goal| {
      Evidence::RowEquation { left, right, goal }
    })
  }
}
