use std::collections::HashSet;

use ena::unify::{EqUnifyValue, UnifyKey};

use crate::ast::Label;
use crate::Evidence;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClosedRow {
  pub fields: Vec<Label>,
  pub values: Vec<Type>,
}
impl ClosedRow {
  /// Merge two disjoint rows into a new row.
  pub fn merge(left: ClosedRow, right: ClosedRow) -> ClosedRow {
    let mut left_fields = left.fields.into_iter().peekable();
    let mut left_values = left.values.into_iter();
    let mut right_fields = right.fields.into_iter().peekable();
    let mut right_values = right.values.into_iter();

    let mut fields = vec![];
    let mut values = vec![];

    // Since our input rows are already sorted we can explit that and not worry about resorting
    // them here, we just have to merge our two sorted rows.
    loop {
      match (left_fields.peek(), right_fields.peek()) {
        (Some(left), Some(right)) => {
          if left <= right {
            fields.push(left_fields.next().unwrap());
            values.push(left_values.next().unwrap());
          } else {
            fields.push(right_fields.next().unwrap());
            values.push(right_values.next().unwrap());
          }
        }
        (Some(_), None) => {
          fields.extend(left_fields);
          values.extend(left_values);
          break;
        }
        (None, Some(_)) => {
          fields.extend(right_fields);
          values.extend(right_values);
          break;
        }
        (None, None) => {
          break;
        }
      }
    }

    ClosedRow { fields, values }
  }

  /// Check if our closed row mentions any of our unbound types or rows.
  pub fn mentions(&self, unbound_tys: &HashSet<TypeUniVar>, unbound_rows: &HashSet<RowUniVar>) -> bool {
    for ty in self.values.iter() {
      if ty.mentions(unbound_tys, unbound_rows) {
        return true;
      }
    }
    false
  }
}
impl EqUnifyValue for ClosedRow {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Row {
  Unifier(RowUniVar),
  Open(RowVar),
  Closed(ClosedRow),
}
impl EqUnifyValue for Row {}
impl Row {
  pub fn single<S: ToString>(lbl: S, ty: Type) -> Self {
    Row::Closed(ClosedRow {
      fields: vec![lbl.to_string()],
      values: vec![ty],
    })
  }

  /// This is not strcit equality (like we get with Eq).
  /// This instead checks a looser sense of equality
  /// that is helpful during unification.
  pub fn equatable(&self, other: &Self) -> bool {
    match (self, other) {
      // Unifier rows are equatable when their variables are equal
      (Row::Unifier(a), Row::Unifier(b)) => a == b,
      // Open rows are equatable when their variables are equal
      (Row::Open(a), Row::Open(b)) => a == b,
      // Closed rows are equatable when their fields are equal
      (Row::Closed(a), Row::Closed(b)) => a.fields == b.fields,
      // Anything else is not equatable
      _ => false,
    }
  }
}

/// Our type
/// Each AST node in our input will be annotated by a value of `Type`
/// after type inference succeeeds.
#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash)]
pub enum Type {
  /// Type of integers
  Int,
  /// A type variable, stands for a value of Type
  Unifier(TypeUniVar),
  /// A rigid type variable, cannot be unified like a normal type variable.
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
  pub fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  pub fn label(label: Label, value: Self) -> Self {
    Self::Label(label, Box::new(value))
  }

  pub fn occurs_check(&self, var: TypeUniVar) -> Result<(), Type> {
    match self {
      Type::Int | Type::Var(_) => Ok(()),
      Type::Unifier(v) => {
        if *v == var {
          Err(Type::Unifier(*v))
        } else {
          Ok(())
        }
      }
      Type::Fun(arg, ret) => {
        arg.occurs_check(var).map_err(|_| self.clone())?;
        ret.occurs_check(var).map_err(|_| self.clone())
      }
      Type::Label(_, ty) => ty.occurs_check(var).map_err(|_| self.clone()),
      Type::Prod(row) | Type::Sum(row) => match row {
        Row::Unifier(_) => Ok(()),
        Row::Open(_) => Ok(()),
        Row::Closed(closed_row) => {
          for ty in closed_row.values.iter() {
            ty.occurs_check(var).map_err(|_| self.clone())?
          }
          Ok(())
        }
      },
    }
  }

  pub fn mentions(&self, unbound_tys: &HashSet<TypeUniVar>, unbound_rows: &HashSet<RowUniVar>) -> bool {
    match self {
      Type::Int | Type::Var(_) => false,
      Type::Unifier(v) => unbound_tys.contains(v),
      Type::Fun(arg, ret) => {
        arg.mentions(unbound_tys, unbound_rows) || ret.mentions(unbound_tys, unbound_rows)
      }
      Type::Label(_, ty) => ty.mentions(unbound_tys, unbound_rows),
      Type::Prod(row) | Type::Sum(row) => match row {
        Row::Unifier(var) => unbound_rows.contains(var),
        // Rigid variables can only exist as bound, so they cannot appear in unbound_rows.
        Row::Open(_) => false,
        Row::Closed(row) => row.mentions(unbound_tys, unbound_rows),
      },
    }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct RowVar(pub u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct RowUniVar {
    pub id: u32,
}
impl RowUniVar {
    pub fn new(id: u32) -> Self {
        Self { id }
    }
}

impl UnifyKey for RowUniVar {
  type Value = Option<Row>;

  fn index(&self) -> u32 {
    self.id
  }

  fn from_index(id: u32) -> Self {
    Self::new(id)
  }

  fn tag() -> &'static str {
    "RowUniVar"
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct TypeVar(pub u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct TypeUniVar {
    pub id: u32,
}
impl TypeUniVar {
    pub fn new(id: u32) -> Self {
        Self { id }
    }

    pub fn rigid(id: u32) -> Self {
        Self { id }
    }
}
impl UnifyKey for TypeUniVar {
  type Value = Option<Type>;

  fn index(&self) -> u32 {
    self.id
  }

  fn from_index(id: u32) -> Self {
    Self::new(id)
  }

  fn tag() -> &'static str {
    "TypeUniVar"
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
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
  pub fn is_unifiable(&self, other: &Self) -> bool {
    let left_equatable = self.left.equatable(&other.left);
    let right_equatable = self.right.equatable(&other.right);
    let goal_equatable = self.goal.equatable(&other.goal);
    (goal_equatable && (left_equatable || right_equatable)) || (left_equatable && right_equatable)
  }

  /// Check unifiability the same way as `is_unifiable` but commutes the arguments.
  /// So we check left against right, and right against left. Goal is still checked against goal.
  pub fn is_comm_unifiable(&self, other: &Self) -> bool {
    let left_equatable = self.left.equatable(&other.right);
    let right_equatable = self.right.equatable(&other.left);
    let goal_equatable = self.goal.equatable(&other.goal);
    (goal_equatable && (left_equatable || right_equatable)) || (left_equatable && right_equatable)
  }

  pub fn into_evidence(self) -> Evidence {
    Evidence::RowEquation { left: self.left, right: self.right, goal: self.goal }
  }
}
