use crate::ast::NodeId;
use crate::ty::{ClosedRow, Row, RowCombination, RowUniVar, RowVar, Type, TypeUniVar, TypeVar};
use crate::{Constraint, Evidence, TypeInference};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeErrorKind {
  TypeNotEqual((Type, Type)),
  InfiniteType(TypeUniVar, Type),
  RowsNotEqual((Row, Row)),
  CheckIntroducedExtraVariablesOrConstraints {
      extra_types: Vec<TypeVar>,
      extra_row: Vec<RowVar>,
      extra_evidence: Vec<Evidence>,
  },
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeError {
  pub kind: TypeErrorKind,
  pub node_id: NodeId,
}

impl From<(ClosedRow, ClosedRow)> for TypeErrorKind {
  fn from((left, right): (ClosedRow, ClosedRow)) -> Self {
    TypeErrorKind::RowsNotEqual((Row::Closed(left), Row::Closed(right)))
  }
}

/// Constraint solving
impl TypeInference {
  pub(crate) fn unification(&mut self, constraints: Vec<Constraint>) -> Result<(), TypeError> {
    for constr in constraints {
      match constr {
        Constraint::TypeEqual(node_id, left, right) => self.unify_ty_ty(left, right).map_err(|kind| TypeError { kind, node_id })?,
        Constraint::RowCombine(node_id, row_comb) => self.unify_row_comb(row_comb).map_err(|kind| TypeError { kind, node_id })?,
      }
    }
    Ok(())
  }

  fn normalize_closed_row(&mut self, closed: ClosedRow) -> ClosedRow {
    ClosedRow {
      fields: closed.fields,
      values: closed
        .values
        .into_iter()
        .map(|ty| self.normalize_ty(ty))
        .collect(),
    }
  }

  fn normalize_row(&mut self, row: Row) -> Row {
    match row {
      Row::Unifier(var) => match self.row_unification_table.probe_value(var) {
        Some(Row::Closed(closed)) => Row::Closed(self.normalize_closed_row(closed)),
        Some(row) => row,
        None => row,
      },
      Row::Open(var) => Row::Open(var),
      Row::Closed(closed) => Row::Closed(self.normalize_closed_row(closed)),
    }
  }

  fn dispatch_any_solved(&mut self, var: RowUniVar, row: ClosedRow) -> Result<(), TypeErrorKind> {
    let mut changed_combs = vec![];
    self.partial_row_combs = std::mem::take(&mut self.partial_row_combs)
      .into_iter()
      .filter_map(|comb| match comb {
        RowCombination { left, right, goal } if left == Row::Unifier(var) => {
          changed_combs.push(RowCombination {
            left: Row::Closed(row.clone()),
            right,
            goal,
          });
          None
        }
        RowCombination { left, right, goal } if right == Row::Unifier(var) => {
          changed_combs.push(RowCombination {
            left,
            right: Row::Closed(row.clone()),
            goal,
          });
          None
        }
        RowCombination { left, right, goal } if goal == Row::Unifier(var) => {
          changed_combs.push(RowCombination {
            left,
            right,
            goal: Row::Closed(row.clone()),
          });
          None
        }
        comb => Some(comb),
      })
      .collect();

    for row_comb in changed_combs {
      self.unify_row_comb(row_comb)?;
    }
    Ok(())
  }

  fn normalize_ty(&mut self, ty: Type) -> Type {
    match ty {
      Type::Int => Type::Int,
      Type::Var(var) => Type::Var(var),
      Type::Fun(arg, ret) => {
        let arg = self.normalize_ty(*arg);
        let ret = self.normalize_ty(*ret);
        Type::fun(arg, ret)
      }
      Type::Unifier(v) => match self.unification_table.probe_value(v) {
        Some(ty) => self.normalize_ty(ty),
        None => Type::Unifier(v),
      },
      Type::Label(label, ty) => {
        let ty = self.normalize_ty(*ty);
        Type::label(label, ty)
      }
      Type::Prod(row) => Type::Prod(self.normalize_row(row)),
      Type::Sum(row) => Type::Sum(self.normalize_row(row)),
    }
  }

  fn unify_ty_ty(&mut self, unnorm_left: Type, unnorm_right: Type) -> Result<(), TypeErrorKind> {
    let left = self.normalize_ty(unnorm_left);
    let right = self.normalize_ty(unnorm_right);
    match (left, right) {
      (Type::Int, Type::Int) => Ok(()),
      (Type::Var(a), Type::Var(b)) => (a == b)
        .then_some(())
        .ok_or(TypeErrorKind::TypeNotEqual((Type::Var(a), Type::Var(b)))),
      (Type::Fun(a_arg, a_ret), Type::Fun(b_arg, b_ret)) => {
        self.unify_ty_ty(*a_arg, *b_arg)?;
        self.unify_ty_ty(*a_ret, *b_ret)
      }
      (Type::Unifier(a), Type::Unifier(b)) => self
        .unification_table
        .unify_var_var(a, b)
        .map_err(TypeErrorKind::TypeNotEqual),
      (Type::Unifier(v), ty) | (ty, Type::Unifier(v)) => {
        ty.occurs_check(v)
          .map_err(|ty| TypeErrorKind::InfiniteType(v, ty))?;
        self
          .unification_table
          .unify_var_value(v, Some(ty))
          .map_err(TypeErrorKind::TypeNotEqual)
      }
      (Type::Prod(left), Type::Prod(right)) | (Type::Sum(left), Type::Sum(right)) => {
        self.unify_row_row(left, right)
      }
      (Type::Label(field, ty), Type::Prod(row))
      | (Type::Prod(row), Type::Label(field, ty))
      | (Type::Label(field, ty), Type::Sum(row))
      | (Type::Sum(row), Type::Label(field, ty)) => self.unify_row_row(
        Row::Closed(ClosedRow {
          fields: vec![field],
          values: vec![*ty],
        }),
        row,
      ),
      (left, right) => Err(TypeErrorKind::TypeNotEqual((left, right))),
    }
  }

  /// Calculate the set difference of the goal row and the sub row, returning it as a new row.
  /// Unify the subset of the goal row that matches the sub row
  fn diff_and_unify(&mut self, goal: ClosedRow, sub: ClosedRow) -> Result<ClosedRow, TypeErrorKind> {
    let mut diff_fields = vec![];
    let mut diff_values = vec![];
    for (field, value) in goal.fields.into_iter().zip(goal.values.into_iter()) {
      match sub.fields.binary_search(&field) {
        Ok(indx) => {
          self.unify_ty_ty(value, sub.values[indx].clone())?;
        }
        Err(_) => {
          diff_fields.push(field);
          diff_values.push(value);
        }
      }
    }
    Ok(ClosedRow {
      fields: diff_fields,
      values: diff_values,
    })
  }

  fn unify_row_row(&mut self, left: Row, right: Row) -> Result<(), TypeErrorKind> {
    let left = self.normalize_row(left);
    let right = self.normalize_row(right);
    match (left, right) {
      (Row::Open(left), Row::Open(right)) => (left == right)
        .then_some(())
        .ok_or(TypeErrorKind::RowsNotEqual((Row::Open(left), Row::Open(right)))),
      (Row::Unifier(left), Row::Unifier(right)) => self
        .row_unification_table
        .unify_var_var(left, right)
        .map_err(TypeErrorKind::RowsNotEqual),
      (Row::Unifier(var), Row::Open(row)) | (Row::Open(row), Row::Unifier(var)) => self
        .row_unification_table
        .unify_var_value(var, Some(Row::Open(row)))
        .map_err(TypeErrorKind::RowsNotEqual),
      (Row::Unifier(var), Row::Closed(row)) | (Row::Closed(row), Row::Unifier(var)) => {
        self
          .row_unification_table
          .unify_var_value(var, Some(Row::Closed(row.clone())))
          .map_err(TypeErrorKind::RowsNotEqual)?;
        self.dispatch_any_solved(var, row)
      }
      (Row::Closed(left), Row::Closed(right)) => {
        // Check that our rows are unifiable
        if left.fields != right.fields {
          return Err(TypeErrorKind::from((left, right)));
        }

        // If they are, our values are already in order so we can walk them and unify the
        // types
        for (left_ty, right_ty) in left.values.into_iter().zip(right.values.into_iter()) {
          self.unify_ty_ty(left_ty, right_ty)?;
        }
        Ok(())
      }
      (Row::Open(var), Row::Closed(row)) | (Row::Closed(row), Row::Open(var)) => {
        Err(TypeErrorKind::RowsNotEqual((Row::Open(var), Row::Closed(row))))
      }
    }
  }

  fn unify_row_comb(&mut self, row_comb: RowCombination) -> Result<(), TypeErrorKind> {
    let left = self.normalize_row(row_comb.left);
    let right = self.normalize_row(row_comb.right);
    let goal = self.normalize_row(row_comb.goal);
    match (left, right, goal) {
      // 0 (and 1) variable(s) case
      (Row::Closed(left), Row::Closed(right), goal) => {
        let calc_goal = ClosedRow::merge(left, right);
        self.unify_row_row(Row::Closed(calc_goal), goal)
      }
      // 1 variable cases
      (Row::Unifier(var), Row::Closed(sub), Row::Closed(goal))
      | (Row::Closed(sub), Row::Unifier(var), Row::Closed(goal)) => {
        let diff_row = self.diff_and_unify(goal, sub)?;
        self.unify_row_row(Row::Unifier(var), Row::Closed(diff_row))
      }
      // 2+ variable cases
      (left, right, goal) => {
        let new_comb = RowCombination { left, right, goal };
        // Check if we've already seen an combination that we can unify against
        let mut poss_uni = None;
        self.partial_row_combs = std::mem::take(&mut self.partial_row_combs).into_iter().map(|comb| {
          let comb = RowCombination {
            left: self.normalize_row(comb.left),
            right: self.normalize_row(comb.right),
            goal: self.normalize_row(comb.goal),
          };
          if comb.is_unifiable(&new_comb) {
            poss_uni = Some(comb.clone());
          //Row combinations commute so we have to check for that possible unification
          } else if comb.is_comm_unifiable(&new_comb) {
            // We commute our combination so we unify the correct rows later
            poss_uni = Some(RowCombination {
              left: comb.right.clone(),
              right: comb.left.clone(),
              goal: comb.goal.clone(),
            });
          }
          comb
        }).collect();

        match poss_uni {
          // Unify if we have a match
          Some(match_comb) => {
            self.unify_row_row(new_comb.left, match_comb.left)?;
            self.unify_row_row(new_comb.right, match_comb.right)?;
            self.unify_row_row(new_comb.goal, match_comb.goal)?;
          }
          // Otherwise add our combination to our list of partial combinations
          None => {
            self.partial_row_combs.insert(new_comb);
          }
        }
        Ok(())
      }
    }
  }
}
