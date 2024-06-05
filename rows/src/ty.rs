use std::collections::HashSet;

use ena::unify::{
  EqUnifyValue, UnifyKey,
};

use crate::ast::Label;

#[derive(
  Debug,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
)]
pub struct ClosedRow {
  pub fields: Vec<Label>,
  pub values: Vec<Type>,
}
impl ClosedRow {
  /// Merge two disjoint rows into a new row.
  pub fn merge(
    left: ClosedRow,
    right: ClosedRow,
  ) -> ClosedRow {
    let mut left_fields =
      left
        .fields
        .into_iter()
        .peekable();
    let mut left_values =
      left.values.into_iter();
    let mut right_fields =
      right
        .fields
        .into_iter()
        .peekable();
    let mut right_values =
      right
        .values
        .into_iter();

    let mut fields = vec![];
    let mut values = vec![];

    // Since our input rows are already sorted we can explit that and not worry about resorting
    // them here, we just have to merge our two sorted rows.
    loop {
      match (
        left_fields.peek(),
        right_fields.peek(),
      ) {
        (
          Some(left),
          Some(right),
        ) => {
          if left <= right {
            fields.push(
              left_fields
                .next()
                .unwrap(),
            );
            values.push(
              left_values
                .next()
                .unwrap(),
            );
          } else {
            fields.push(
              right_fields
                .next()
                .unwrap(),
            );
            values.push(
              right_values
                .next()
                .unwrap(),
            );
          }
        }
        (Some(_), None) => {
          fields.extend(
            left_fields,
          );
          values.extend(
            left_values,
          );
          break;
        }
        (None, Some(_)) => {
          fields.extend(
            right_fields,
          );
          values.extend(
            right_values,
          );
          break;
        }
        (None, None) => {
          break;
        }
      }
    }

    ClosedRow {
      fields,
      values,
    }
  }

  /// Check if our closed row mentions any of our unbound types or rows.
  pub fn mentions(
    &self,
    unbound_tys: &HashSet<
      TypeVar,
    >,
    unbound_rows: &HashSet<
      RowVar,
    >,
  ) -> bool {
    for ty in
      self.values.iter()
    {
      if ty.mentions(
        unbound_tys,
        unbound_rows,
      ) {
        return true;
      }
    }
    false
  }
}
impl EqUnifyValue
  for ClosedRow
{
}

#[derive(
  Debug,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
)]
pub enum Row {
  Open(RowVar),
  Closed(ClosedRow),
}
impl Row {
  pub fn single(
    lbl: Label,
    ty: Type,
  ) -> Self {
    Row::Closed(ClosedRow {
      fields: vec![lbl],
      values: vec![ty],
    })
  }

  /// This is not strcit equality (like we get with Eq).
  /// This instead checks a looser sense of equality
  /// that is helpful during unification.
  pub fn equatable(
    &self,
    other: &Self,
  ) -> bool {
    match (self, other) {
      // Open rows are equatable when their variables are equal
      (
        Row::Open(a),
        Row::Open(b),
      ) => a == b,
      // Closed rows are equatable when their fields are equal
      (
        Row::Closed(a),
        Row::Closed(b),
      ) => {
        a.fields == b.fields
      }
      // Anything else is not equatable
      _ => false,
    }
  }
}

/// Our type
/// Each AST node in our input will be annotated by a value of `Type`
/// after type inference succeeeds.
#[derive(
  PartialEq,
  Eq,
  Clone,
  Debug,
  PartialOrd,
  Ord,
)]
pub enum Type {
  /// Type of integers
  Int,
  /// A type variable, stands for a value of Type
  Var(TypeVar),
  /// A function type
  Fun(Box<Self>, Box<Self>),
  /// A product type
  Prod(Row),
  /// A sum type
  Sum(Row),
  /// Type of singleton rows
  Label(Label, Box<Self>),
}
impl EqUnifyValue for Type {}
impl Type {
  pub fn fun(
    arg: Self,
    ret: Self,
  ) -> Self {
    Self::Fun(
      Box::new(arg),
      Box::new(ret),
    )
  }

  pub fn label(
    label: Label,
    value: Self,
  ) -> Self {
    Self::Label(
      label,
      Box::new(value),
    )
  }

  pub fn occurs_check(
    &self,
    var: TypeVar,
  ) -> Result<(), Type> {
    match self {
      Type::Int => Ok(()),
      Type::Var(v) => {
        if *v == var {
          Err(Type::Var(*v))
        } else {
          Ok(())
        }
      }
      Type::Fun(arg, ret) => {
        arg
          .occurs_check(var)
          .map_err(|_| {
            self.clone()
          })?;
        ret
          .occurs_check(var)
          .map_err(|_| {
            self.clone()
          })
      }
      Type::Label(_, ty) => {
        ty.occurs_check(var)
          .map_err(|_| {
            self.clone()
          })
      }
      Type::Prod(row)
      | Type::Sum(row) => {
        match row {
          Row::Open(_) => {
            Ok(())
          }
          Row::Closed(
            closed_row,
          ) => {
            for ty in
              closed_row
                .values
                .iter()
            {
              ty.occurs_check(
                var,
              )
              .map_err(
                |_| {
                  self.clone()
                },
              )?
            }
            Ok(())
          }
        }
      }
    }
  }

  pub fn mentions(
    &self,
    unbound_tys: &HashSet<
      TypeVar,
    >,
    unbound_rows: &HashSet<
      RowVar,
    >,
  ) -> bool {
    match self {
      Type::Int => false,
      Type::Var(v) => {
        unbound_tys
          .contains(v)
      }
      Type::Fun(arg, ret) => {
        arg.mentions(
          unbound_tys,
          unbound_rows,
        ) || ret.mentions(
          unbound_tys,
          unbound_rows,
        )
      }
      Type::Label(_, ty) => {
        ty.mentions(
          unbound_tys,
          unbound_rows,
        )
      }
      Type::Prod(row)
      | Type::Sum(row) => {
        match row {
          Row::Open(var) => {
            unbound_rows
              .contains(var)
          }
          Row::Closed(
            row,
          ) => row.mentions(
            unbound_tys,
            unbound_rows,
          ),
        }
      }
    }
  }
}

#[derive(
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Clone,
  Copy,
  Debug,
  Hash,
)]
pub struct RowVar(pub u32);
impl UnifyKey for RowVar {
  type Value =
    Option<ClosedRow>;

  fn index(&self) -> u32 {
    self.0
  }

  fn from_index(
    u: u32,
  ) -> Self {
    Self(u)
  }

  fn tag() -> &'static str {
    "TypeVar"
  }
}

#[derive(
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Clone,
  Copy,
  Debug,
  Hash,
)]
pub struct TypeVar(pub u32);
impl UnifyKey for TypeVar {
  type Value = Option<Type>;

  fn index(&self) -> u32 {
    self.0
  }

  fn from_index(
    u: u32,
  ) -> Self {
    Self(u)
  }

  fn tag() -> &'static str {
    "TypeVar"
  }
}

#[derive(
  Debug,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Clone,
)]
pub struct RowCombination {
  pub left: Row,
  pub right: Row,
  pub goal: Row,
}
impl RowCombination {
  /// Two rows are unifiable if two of their components are equatable.
  /// A row can be uniquely determined by two of it's components (the third is calculated from
  /// the two). Because of this whenever rows agree on two components we can unify both rows and
  /// possible learn new information about the third row.
  ///
  /// This only works because our row combinations are commutative.
  pub fn is_unifiable(
    &self,
    other: &Self,
  ) -> bool {
    let left_equatable = self
      .left
      .equatable(&other.left);
    let right_equatable =
      self.right.equatable(
        &other.right,
      );
    let goal_equatable = self
      .goal
      .equatable(&other.goal);
    (goal_equatable
      && (left_equatable
        || right_equatable))
      || (left_equatable
        && right_equatable)
  }

  /// Check unifiability the same way as `is_unifiable` but commutes the arguments.
  /// So we check left against right, and right against left. Goal is still checked against goal.
  pub fn is_comm_unifiable(
    &self,
    other: &Self,
  ) -> bool {
    let left_equatable =
      self.left.equatable(
        &other.right,
      );
    let right_equatable =
      self.right.equatable(
        &other.left,
      );
    let goal_equatable = self
      .goal
      .equatable(&other.goal);
    (goal_equatable
      && (left_equatable
        || right_equatable))
      || (left_equatable
        && right_equatable)
  }
}
