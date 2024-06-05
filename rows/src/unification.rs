use std::cmp::Ordering;
use std::collections::BTreeSet;

use itertools::Itertools;

use crate::ty::{ClosedRow, Data, Eff, Row, RowCombination, RowStyle, RowVar, Type, TypeVar};
use crate::{Constraint, TypeInference};

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
  TypeNotEqual((Type, Type)),
  InfiniteType(TypeVar, Type),
  RowsNotEqual((ClosedRow, ClosedRow)),
  UnsolvedHandle(RowVar, Row),
  UndefinedHandler(ClosedRow),
}

/// Constraint solving
impl TypeInference {
  pub(crate) fn unification(&mut self, constraints: Vec<Constraint>) -> Result<(), TypeError> {
    for constr in constraints {
      match constr {
        Constraint::TypeEqual(left, right) => self.unify_ty_ty(left, right)?,
        Constraint::DataEqual(left, right) => self.unify_row_row::<Data>(left, right)?,
        Constraint::EffEqual(left, right) => self.unify_row_row::<Eff>(left, right)?,
        Constraint::DataCombo(row_comb) => self.unify_data_row_comb(row_comb)?,
        Constraint::EffCombo(row_comb) => self.unify_eff_row_comb(row_comb)?,
        Constraint::Handles { handler, eff, ret } => self.unify_handles(handler, eff, ret)?,
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
      Row::Open(var) => {
        let root = self.row_unification_table.find(var);
        match self.row_unification_table.probe_value(root) {
          Some(closed) => Row::Closed(self.normalize_closed_row(closed)),
          None => Row::Open(root),
        }
      }
      Row::Closed(closed) => Row::Closed(self.normalize_closed_row(closed)),
    }
  }

  fn dispatch_any_solved<R: RowStyle>(
    &mut self,
    var: RowVar,
    row: ClosedRow,
  ) -> Result<(), TypeError>
  where
    Self: RowSolver<R>,
  {
    let mut changed_combs = vec![];
    self.with_partial_row_combs(|row_combos| {
      row_combos
        .into_iter()
        .filter_map(|comb: RowCombination<R>| match comb {
          RowCombination {
            left, right, goal, ..
          } if left == Row::Open(var) => {
            changed_combs.push(RowCombination::new(Row::Closed(row.clone()), right, goal));
            None
          }
          RowCombination {
            left, right, goal, ..
          } if right == Row::Open(var) => {
            changed_combs.push(RowCombination::new(left, Row::Closed(row.clone()), goal));
            None
          }
          RowCombination {
            left, right, goal, ..
          } if goal == Row::Open(var) => {
            changed_combs.push(RowCombination::new(left, right, Row::Closed(row.clone())));
            None
          }
          comb => Some(comb),
        })
        .collect()
    });

    for row_comb in changed_combs {
      self.unify_row_comb(row_comb)?;
    }
    Ok(())
  }

  fn normalize_ty(&mut self, ty: Type) -> Type {
    match ty {
      Type::Int => Type::Int,
      Type::Fun(arg, ret) => {
        let arg = self.normalize_ty(*arg);
        let ret = self.normalize_ty(*ret);
        Type::fun(arg, ret)
      }
      Type::Var(v) => {
        let root = self.unification_table.find(v);
        match self.unification_table.probe_value(root) {
          Some(ty) => self.normalize_ty(ty),
          None => Type::Var(root),
        }
      }
      Type::Label(label, ty) => {
        let ty = self.normalize_ty(*ty);
        Type::label(label, ty)
      }
      Type::Prod(row) => Type::Prod(self.normalize_row(row)),
      Type::Sum(row) => Type::Sum(self.normalize_row(row)),
    }
  }

  fn unify_ty_ty(&mut self, unnorm_left: Type, unnorm_right: Type) -> Result<(), TypeError> {
    let left = self.normalize_ty(unnorm_left);
    let right = self.normalize_ty(unnorm_right);
    match (left, right) {
      (Type::Int, Type::Int) => Ok(()),
      (Type::Fun(a_arg, a_ret), Type::Fun(b_arg, b_ret)) => {
        self.unify_ty_ty(*a_arg, *b_arg)?;
        self.unify_ty_ty(*a_ret, *b_ret)
      }
      (Type::Var(a), Type::Var(b)) => self
        .unification_table
        .unify_var_var(a, b)
        .map_err(TypeError::TypeNotEqual),
      (Type::Var(v), ty) | (ty, Type::Var(v)) => {
        ty.occurs_check(v)
          .map_err(|ty| TypeError::InfiniteType(v, ty))?;
        self
          .unification_table
          .unify_var_value(v, Some(ty))
          .map_err(TypeError::TypeNotEqual)
      }
      (Type::Prod(left), Type::Prod(right)) | (Type::Sum(left), Type::Sum(right)) => {
        self.unify_row_row::<Data>(left, right)
      }
      (Type::Label(field, ty), Type::Prod(row))
      | (Type::Prod(row), Type::Label(field, ty))
      | (Type::Label(field, ty), Type::Sum(row))
      | (Type::Sum(row), Type::Label(field, ty)) => self.unify_row_row::<Data>(
        Row::Closed(ClosedRow {
          fields: vec![field],
          values: vec![*ty],
        }),
        row,
      ),
      (left, right) => Err(TypeError::TypeNotEqual((left, right))),
    }
  }

  /// Calculate the set difference of the goal row and the sub row, returning it as a new row.
  /// Unify the subset of the goal row that matches the sub row
  fn diff_and_unify(&mut self, goal: ClosedRow, sub: ClosedRow) -> Result<ClosedRow, TypeError> {
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

  fn difference_rowlikes(
    &mut self,
    goal: ClosedRow,
    sub: ClosedRow,
    mut split_groups: impl for<'a> FnMut(
      Vec<&'a (String, Type)>,
      &Vec<&(String, Type)>,
    ) -> (Vec<&'a (String, Type)>, Vec<&'a (String, Type)>),
  ) -> Result<ClosedRow, TypeError> {
    let goal_vec = goal.fields.into_iter().zip(goal.values).collect::<Vec<_>>();
    let goal_groups = goal_vec.iter().group_by(|(field, _)| field.as_str());
    let sub_vec = sub.fields.into_iter().zip(sub.values).collect::<Vec<_>>();
    let sub_groups = sub_vec.iter().group_by(|pair| pair.0.as_str());

    let (mut fields, mut values) = (vec![], vec![]);

    for (sub_key, sub_group) in &sub_groups {
      let sub_group = sub_group.into_iter().collect::<Vec<_>>();
      for (goal_key, goal_group) in &goal_groups {
        match goal_key.cmp(sub_key) {
          Ordering::Less => {
            goal_group.into_iter().for_each(|(field, value)| {
              fields.push(field.clone());
              values.push(value.clone());
            });
          }
          Ordering::Equal => {
            let goal_group = goal_group.into_iter().collect::<Vec<_>>();
            let (sub_goal_row, other_group) = split_groups(goal_group, &sub_group);
            // IMPORTANT: Unify our sub row and the sub of our goal row
            for (left, right) in sub_group.clone().into_iter().zip(sub_goal_row.into_iter()) {
              self.unify_ty_ty(left.1.clone(), right.1.clone())?;
            }
            fields.extend(other_group.iter().map(|(field, _)| field.clone()));
            values.extend(other_group.iter().map(|(_, value)| value.clone()));
            break;
          }
          Ordering::Greater => {
            unreachable!("Sub row contains fields goal row did not")
          }
        }
      }
    }

    for (_, goal_group) in &goal_groups {
      goal_group.into_iter().for_each(|(field, value)| {
        fields.push(field.clone());
        values.push(value.clone());
      })
    }

    fields.shrink_to_fit();
    values.shrink_to_fit();

    Ok(ClosedRow { fields, values })
  }

  fn diff_left_and_unify(
    &mut self,
    goal: ClosedRow,
    left: ClosedRow,
  ) -> Result<ClosedRow, TypeError> {
    self.difference_rowlikes(goal, left, |mut goal, left| {
      let split = left.len();
      let right = goal.split_off(split);
      (goal, right)
    })
  }

  fn diff_right_and_unify(
    &mut self,
    goal: ClosedRow,
    right: ClosedRow,
  ) -> Result<ClosedRow, TypeError> {
    self.difference_rowlikes(goal, right, |mut goal, right| {
      let split = goal.len() - right.len();
      let right = goal.split_off(split);
      (right, goal)
    })
  }

  fn unify_row_row<R: RowStyle>(&mut self, left: Row, right: Row) -> Result<(), TypeError>
  where
    Self: RowSolver<R>,
  {
    let left = self.normalize_row(left);
    let right = self.normalize_row(right);
    match (left, right) {
      (Row::Open(left), Row::Open(right)) => {
        println!("unify_row_row: {:?} ~ {:?}", left, right);
        self
          .row_unification_table
          .unify_var_var(left, right)
          .map_err(TypeError::RowsNotEqual)
      }
      (Row::Open(var), Row::Closed(row)) | (Row::Closed(row), Row::Open(var)) => {
        self
          .row_unification_table
          .unify_var_value(var, Some(row.clone()))
          .map_err(TypeError::RowsNotEqual)?;
        self.dispatch_any_solved::<R>(var, row)
      }
      (Row::Closed(left), Row::Closed(right)) => {
        // Check that our rows are unifiable
        if left.fields != right.fields {
          return Err(TypeError::RowsNotEqual((left, right)));
        }

        // If they are, our values are already in order so we can walk them and unify the
        // types
        for (left_ty, right_ty) in left.values.into_iter().zip(right.values.into_iter()) {
          self.unify_ty_ty(left_ty, right_ty)?;
        }
        Ok(())
      }
    }
  }

  fn unify_eff_row_comb(&mut self, row_comb: RowCombination<Eff>) -> Result<(), TypeError> {
    let left = self.normalize_row(row_comb.left.clone());
    let right = self.normalize_row(row_comb.right.clone());
    let goal = self.normalize_row(row_comb.goal.clone());
    println!(
      "unify_eff_row_comb: ({:?} -> {:?}) * ({:?} -> {:?}) ~ ({:?} -> {:?})",
      row_comb.left, left, row_comb.right, right, row_comb.goal, goal
    );
    match (left, right, goal) {
      // 0 (and 1) variable(s) case
      (Row::Closed(left), Row::Closed(right), goal) => {
        let calc_goal = ClosedRow::merge(left, right);
        self.unify_row_row::<Eff>(Row::Closed(calc_goal), goal)
      }
      // 1 variable cases
      // Order matters for effect rows because they are scoped rows,
      // so we have two separate cases (vs 1 for data rows).
      (Row::Open(left), Row::Closed(right), Row::Closed(goal)) => {
        let diff_left = self.diff_right_and_unify(goal, right)?;
        self.unify_row_row::<Eff>(Row::Open(left), Row::Closed(diff_left))
      }
      (Row::Closed(left), Row::Open(right), Row::Closed(goal)) => {
        let diff_right = self.diff_left_and_unify(goal, left)?;
        self.unify_row_row::<Eff>(Row::Open(right), Row::Closed(diff_right))
      }
      (left, right, goal) => {
        let new_comb = RowCombination::new(left, right, goal);
        // Check if we've already seen a combination that we can unify against
        let poss_uni = self.partial_eff_row_combs.iter().find_map(|comb| {
          // Effect rows don't commute so we only check one ordering is unifiable
          comb.is_unifiable(&new_comb).then(|| comb.clone())
        });

        match poss_uni {
          // Unify if we have a match
          Some(match_comb) => {
            self.unify_row_row::<Eff>(new_comb.left, match_comb.left)?;
            self.unify_row_row::<Eff>(new_comb.right, match_comb.right)?;
            self.unify_row_row::<Eff>(new_comb.goal, match_comb.goal)?;
          }
          // Otherwise add our combination to our list of partial combinations
          None => {
            self.partial_eff_row_combs.insert(new_comb);
          }
        }
        Ok(())
      }
    }
  }

  fn unify_data_row_comb(&mut self, row_comb: RowCombination<Data>) -> Result<(), TypeError> {
    let left = self.normalize_row(row_comb.left);
    let right = self.normalize_row(row_comb.right);
    let goal = self.normalize_row(row_comb.goal);
    match (left, right, goal) {
      // 0 (and 1) variable(s) case
      (Row::Closed(left), Row::Closed(right), goal) => {
        let calc_goal = ClosedRow::merge(left, right);
        self.unify_row_row::<Data>(Row::Closed(calc_goal), goal)
      }
      // 1 variable cases
      (Row::Open(var), Row::Closed(sub), Row::Closed(goal))
      | (Row::Closed(sub), Row::Open(var), Row::Closed(goal)) => {
        let diff_row = self.diff_and_unify(goal, sub)?;
        self.unify_row_row::<Data>(Row::Open(var), Row::Closed(diff_row))
      }
      // 2+ variable cases
      (left, right, goal) => {
        let new_comb = RowCombination::new(left, right, goal);
        // Check if we've already seen an combination that we can unify against
        let poss_uni = self.partial_data_row_combs.iter().find_map(|comb| {
          if comb.is_unifiable(&new_comb) {
            Some(comb.clone())
          //Row combinations commute so we have to check for that possible unification
          } else if comb.is_comm_unifiable(&new_comb) {
            // We commute our combination so we unify the correct rows later
            Some(RowCombination::new(
              comb.right.clone(),
              comb.left.clone(),
              comb.goal.clone(),
            ))
          } else {
            None
          }
        });

        match poss_uni {
          // Unify if we have a match
          Some(match_comb) => {
            self.unify_row_row::<Data>(new_comb.left, match_comb.left)?;
            self.unify_row_row::<Data>(new_comb.right, match_comb.right)?;
            self.unify_row_row::<Data>(new_comb.goal, match_comb.goal)?;
          }
          // Otherwise add our combination to our list of partial combinations
          None => {
            self.partial_data_row_combs.insert(new_comb);
          }
        }
        Ok(())
      }
    }
  }

  fn unify_handles(&mut self, handler: Row, eff: Row, ret: Type) -> Result<(), TypeError> {
    let handler = self.normalize_row(handler);
    let eff = self.normalize_row(eff);
    let ret = self.normalize_ty(ret);

    // We make a simplifying assumption here that our handler must be concrete and solved by
    // unification. We can't be polymorphic in terms of our handler. We're allowed to keep a
    // handler in a variable (we can do some unification to get to our handler) but it has to be
    // resolved by the time we handle this constraint.
    let (handler_ty, eff_name) = match (handler, eff.clone()) {
      (Row::Closed(handler_row), Row::Closed(eff_row)) => {
        let eff_name = eff_row.fields[0].clone();

        let eff_ret = eff_row.values[0].clone();
        self.unify_ty_ty(ret.clone(), eff_ret)?;
        (Type::Prod(Row::Closed(handler_row)), eff_name)
      }
      (Row::Closed(handler_row), Row::Open(eff_var)) => {
        let eff_name = self
          .lookup_effect_by_handler(handler_row.fields.as_slice())
          .ok_or_else(|| TypeError::UndefinedHandler(handler_row.clone()))?;

        self.unify_row_row::<Eff>(
          Row::Open(eff_var),
          Row::Closed(ClosedRow {
            fields: vec![eff_name.clone()],
            values: vec![ret.clone()],
          }),
        )?;
        (Type::Prod(Row::Closed(handler_row)), eff_name)
      }
      (Row::Open(handler), eff) => return Err(TypeError::UnsolvedHandle(handler, eff)),
    };
    let eff_sig = self.effect_handler_signature(eff_name);

    let eff_ret = eff_sig.ret_ty;
    let (eff_row, ty_inst, _) = self.instantiate(eff_sig.into_scheme());
    self.unify_ty_ty(Type::Var(ty_inst[&eff_ret]), ret)?;
    self.unify_ty_ty(handler_ty, eff_row)?;

    Ok(())
  }
}

/// Methods required to accomplish solve rows for a style.
///
/// Previously we just hardcoded these methods when we just had Data rows, but now that we have
/// data and effect rows it's helpful to combine them under a trait.
trait RowSolver<R: RowStyle> {
  /// Modify our partial row combinator set for this row style
  fn with_partial_row_combs(
    &mut self,
    body: impl FnOnce(BTreeSet<RowCombination<R>>) -> BTreeSet<RowCombination<R>>,
  );
  /// Unify a row combination producing any partial row combinations and dispatching newly solved
  /// rows.
  fn unify_row_comb(&mut self, row_comb: RowCombination<R>) -> Result<(), TypeError>;
}

impl RowSolver<Data> for TypeInference {
  fn with_partial_row_combs(
    &mut self,
    body: impl FnOnce(BTreeSet<RowCombination<Data>>) -> BTreeSet<RowCombination<Data>>,
  ) {
    self.partial_data_row_combs = body(std::mem::take(&mut self.partial_data_row_combs));
  }

  fn unify_row_comb(&mut self, row_comb: RowCombination<Data>) -> Result<(), TypeError> {
    let left = self.normalize_row(row_comb.left);
    let right = self.normalize_row(row_comb.right);
    let goal = self.normalize_row(row_comb.goal);
    match (left, right, goal) {
      // 0 (and 1) variable(s) case
      (Row::Closed(left), Row::Closed(right), goal) => {
        let calc_goal = ClosedRow::merge(left, right);
        self.unify_row_row::<Data>(Row::Closed(calc_goal), goal)
      }
      // 1 variable cases
      (Row::Open(var), Row::Closed(sub), Row::Closed(goal))
      | (Row::Closed(sub), Row::Open(var), Row::Closed(goal)) => {
        let diff_row = self.diff_and_unify(goal, sub)?;
        self.unify_row_row::<Data>(Row::Open(var), Row::Closed(diff_row))
      }
      // 2+ variable cases
      (left, right, goal) => {
        let new_comb = RowCombination::new(left, right, goal);
        // Check if we've already seen an combination that we can unify against
        let poss_uni = self.partial_data_row_combs.iter().find_map(|comb| {
          if comb.is_unifiable(&new_comb) {
            Some(comb.clone())
          //Row combinations commute so we have to check for that possible unification
          } else if comb.is_comm_unifiable(&new_comb) {
            // We commute our combination so we unify the correct rows later
            Some(RowCombination::new(
              comb.right.clone(),
              comb.left.clone(),
              comb.goal.clone(),
            ))
          } else {
            None
          }
        });

        match poss_uni {
          // Unify if we have a match
          Some(match_comb) => {
            self.unify_row_row::<Data>(new_comb.left, match_comb.left)?;
            self.unify_row_row::<Data>(new_comb.right, match_comb.right)?;
            self.unify_row_row::<Data>(new_comb.goal, match_comb.goal)?;
          }
          // Otherwise add our combination to our list of partial combinations
          None => {
            self.partial_data_row_combs.insert(new_comb);
          }
        }
        Ok(())
      }
    }
  }
}

impl RowSolver<Eff> for TypeInference {
  fn with_partial_row_combs(
    &mut self,
    body: impl FnOnce(BTreeSet<RowCombination<Eff>>) -> BTreeSet<RowCombination<Eff>>,
  ) {
    self.partial_eff_row_combs = body(std::mem::take(&mut self.partial_eff_row_combs));
  }

  fn unify_row_comb(&mut self, row_comb: RowCombination<Eff>) -> Result<(), TypeError> {
    let left = self.normalize_row(row_comb.left);
    let right = self.normalize_row(row_comb.right);
    let goal = self.normalize_row(row_comb.goal);
    match (left, right, goal) {
      // 0 (and 1) variable(s) case
      (Row::Closed(left), Row::Closed(right), goal) => {
        let goal_closed = ClosedRow::merge(left, right);
        self.unify_row_row::<Eff>(Row::Closed(goal_closed), goal)
      }
      // 1 variable cases
      // Order matters for effect rows because they are scoped rows,
      // so we have two separate cases (vs 1 for data rows).
      (Row::Open(left), Row::Closed(right), Row::Closed(goal)) => {
        let left_closed = self.diff_right_and_unify(goal, right)?;
        self.unify_row_row::<Eff>(Row::Open(left), Row::Closed(left_closed))
      }
      (Row::Closed(left), Row::Open(right), Row::Closed(goal)) => {
        let right_closed = self.diff_left_and_unify(goal, left)?;
        self.unify_row_row::<Eff>(Row::Open(right), Row::Closed(right_closed))
      }
      (left, right, goal) => {
        let new_comb = RowCombination::new(left, right, goal);
        // Check if we've already seen a combination that we can unify against
        let poss_uni = self.partial_eff_row_combs.iter().find_map(|comb| {
          // Effect rows don't commute so we only check one ordering is unifiable
          comb.is_unifiable(&new_comb).then(|| comb.clone())
        });

        match poss_uni {
          // Unify if we have a match
          Some(match_comb) => {
            self.unify_row_row::<Eff>(new_comb.left, match_comb.left)?;
            self.unify_row_row::<Eff>(new_comb.right, match_comb.right)?;
            self.unify_row_row::<Eff>(new_comb.goal, match_comb.goal)?;
          }
          // Otherwise add our combination to our list of partial combinations
          None => {
            self.partial_eff_row_combs.insert(new_comb);
          }
        }
        Ok(())
      }
    }
  }
}
