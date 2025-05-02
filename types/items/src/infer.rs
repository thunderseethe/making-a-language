use std::collections::HashMap;
use std::ops::Deref;

use crate::ast::{Ast, Direction, ItemWrapper, TypedVar, Var};
use crate::inst::Instantiate;
use crate::ty::{Row, RowCombination, RowUniVar, Type, TypeUniVar};
use crate::{Constraint, Evidence, TypeInference};

pub struct InferOut {
  pub constraints: Vec<Constraint>,
  pub typed_ast: Ast<TypedVar>,
}
impl InferOut {
  fn with_typed_ast(self, f: impl FnOnce(Ast<TypedVar>) -> Ast<TypedVar>) -> Self {
    InferOut {
      constraints: self.constraints,
      typed_ast: f(self.typed_ast),
    }
  }
}

impl InferOut {
  fn new(constraints: Vec<Constraint>, typed_ast: Ast<TypedVar>) -> Self {
    Self {
      constraints,
      typed_ast,
    }
  }
}

/// Constraint generation
impl TypeInference {
  /// Create a unique type variable
  fn fresh_ty_var(&mut self) -> TypeUniVar {
    self.unification_table.new_key(None)
  }

  /// Create a unique row variable
  fn fresh_row_var(&mut self) -> RowUniVar {
    self.row_unification_table.new_key(None)
  }

  /// Create a row combination with fresh row variables
  fn fresh_row_combination(&mut self) -> RowCombination {
    RowCombination {
      left: Row::Unifier(self.fresh_row_var()),
      right: Row::Unifier(self.fresh_row_var()),
      goal: Row::Unifier(self.fresh_row_var()),
    }
  }

  /// Infer type of `ast`
  /// Returns a list of constraints that need to be true and the type `ast` will have if
  /// constraints hold.
  pub(crate) fn infer(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>) -> (InferOut, Type) {
    match ast {
      Ast::Int(id, i) => (InferOut::new(vec![], Ast::Int(id, i)), Type::Int),
      Ast::Var(id, v) => {
        let ty = &env[&v];
        (
          InferOut::new(vec![], Ast::Var(id, TypedVar(v, ty.clone()))),
          ty.clone(),
        )
      }
      Ast::Fun(id, arg, body) => {
        let arg_ty_var = self.fresh_ty_var();
        let env = env.update(arg, Type::Unifier(arg_ty_var));
        let (body_out, body_ty) = self.infer(env, *body);
        (
          InferOut {
            typed_ast: Ast::fun(id, TypedVar(arg, Type::Unifier(arg_ty_var)), body_out.typed_ast),
            ..body_out
          },
          Type::fun(Type::Unifier(arg_ty_var), body_ty),
        )
      }
      Ast::App(id, fun, arg) => {
        let (arg_out, arg_ty) = self.infer(env.clone(), *arg);

        let ret_ty = Type::Unifier(self.fresh_ty_var());
        let fun_ty = Type::fun(arg_ty, ret_ty.clone());

        let fun_out = self.check(env, *fun, fun_ty);

        (
          InferOut::new(
            arg_out
              .constraints
              .into_iter()
              .chain(fun_out.constraints)
              .collect(),
            Ast::app(id, fun_out.typed_ast, arg_out.typed_ast),
          ),
          ret_ty,
        )
      }
      // Labeling
      Ast::Label(id, label, value) => {
        let (out, value_ty) = self.infer(env, *value);
        (
          out.with_typed_ast(|ast| Ast::label(id, label.clone(), ast)),
          Type::label(label, value_ty),
        )
      }
      Ast::Unlabel(id, value, label) => {
        let value_var = self.fresh_ty_var();
        let expected_ty = Type::label(label.clone(), Type::Unifier(value_var));
        let out = self.check(env, *value, expected_ty);
        ( out.with_typed_ast(|ast| Ast::unlabel(id, ast, label))
        , Type::Unifier(value_var)
        )
      }
      // Products
      Ast::Concat(id, left, right) => {
        let row_comb = self.fresh_row_combination();

        // Concat combines two smaller rows into a larger row.
        // To check this we check that our inputs have the types of our smaller rows left
        // and right.
        let left_out = self.check(env.clone(), *left, Type::Prod(row_comb.left.clone()));
        let right_out = self.check(env, *right, Type::Prod(row_comb.right.clone()));

        // If they do, then our output type is our big row goal
        let out_ty = Type::Prod(row_comb.goal.clone());
        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        // Add a new constraint for our row combination to solve concat
        constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);

        let typed_ast = Ast::concat(
          id, 
          left_out.typed_ast,
          right_out.typed_ast,
        );

        (
          InferOut {
            constraints,
            typed_ast,
          },
          out_ty,
        )
      }
      Ast::Project(id, dir, goal) => {
        let row_comb = self.fresh_row_combination();
        // Based on the direction of our projection,
        // our output row is either left or right
        let sub_row = match dir {
          Direction::Left => row_comb.left.clone(),
          Direction::Right => row_comb.right.clone(),
        };
        // Project transforms a row into a subset of its fields, so we check our goal ast
        // node against our goal row (not our sub_row)
        let mut out = self.check(env, *goal, Type::Prod(row_comb.goal.clone()));
        // Add our row combination constraint to solve our projection
        out
          .constraints
          .push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);
        (
          out.with_typed_ast(|ast| Ast::project(id, dir, ast)),
          // Our sub row is the output type of the projection
          Type::Prod(sub_row),
        )
      }
      // Sums
      Ast::Branch(id, left, right) => {
        let row_comb = self.fresh_row_combination();
        let ret_ty = self.fresh_ty_var();

        // Branch expects it's two inputs to be handling functions
        // with type: <sum> -> a
        // So we check that our left and right AST both have handler function types that
        // agree on return type
        let left_out = self.check(
          env.clone(),
          *left,
          Type::fun(Type::Sum(row_comb.left.clone()), Type::Unifier(ret_ty)),
        );
        let right_out = self.check(
          env,
          *right,
          Type::fun(Type::Sum(row_comb.right.clone()), Type::Unifier(ret_ty)),
        );

        // If they do the overall type of our Branch node is a function from our goal row
        // sum type to our return type
        let out_ty = Type::fun(Type::Sum(row_comb.goal.clone()), Type::Unifier(ret_ty));
        // Collect all our constraints for our final output
        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);
        self.branch_to_ret_ty.insert(id, Type::Unifier(ret_ty));

        (
          InferOut {
            constraints,
            typed_ast: Ast::branch(
              id,
              left_out.typed_ast,
              right_out.typed_ast,
            ),
          },
          out_ty,
        )
      }
      Ast::Inject(id, dir, value) => {
        let row_comb = self.fresh_row_combination();
        // Like project, inject works in terms of sub rows and goal rows.
        // But inject is _injecting_ a smaller row into a bigger row.
        let sub_row = match dir {
          Direction::Left => row_comb.left.clone(),
          Direction::Right => row_comb.right.clone(),
        };

        let out_ty = Type::Sum(row_comb.goal.clone());
        // Because of this our sub row is the type of our value
        let mut out = self.check(env, *value, Type::Sum(sub_row));
        out
          .constraints
          .push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);
        (
          out.with_typed_ast(|ast| Ast::inject(id, dir, ast)),
          // Our goal row is the type of our output
          out_ty,
        )
      }
      Ast::Item(id, item_id) => {
        let ty_scheme = self.item_source.type_of_item(item_id);

        // Create fresh unifiers for each type and row variable in our type scheme.
        let mut wrapper_tyvars = vec![];
        let tyvar_to_unifiers = ty_scheme
          .unbound_tys
          .iter()
          .map(|ty_var| {
            let unifier = self.fresh_ty_var();
            wrapper_tyvars.push(Type::Unifier(unifier));
            (*ty_var, unifier)
          })
          .collect::<HashMap<_, _>>();
        let mut wrapper_rowvars = vec![];
        let rowvar_to_unifiers = ty_scheme
          .unbound_rows
          .iter()
          .map(|row_var| {
            let unifier = self.fresh_row_var();
            wrapper_rowvars.push(Row::Unifier(unifier));
            (*row_var, unifier)
          })
          .collect::<HashMap<_, _>>();

        // Instantiate our scheme mapping it's variables to the fresh unifiers we just generated.
        // After this we'll have a list of constraints and a type that only reference the fresh
        // unfiers.
        let (constraints, ty) =
          Instantiate::new(id, &tyvar_to_unifiers, &rowvar_to_unifiers).type_scheme(ty_scheme);
        let wrapper = ItemWrapper {
          types: wrapper_tyvars,
          rows: wrapper_rowvars,
          evidence: constraints
            .clone()
            .into_iter()
            .filter_map(|c| match c {
              Constraint::RowCombine(_, row_combo) => Some(Evidence::RowEquation {
                left: row_combo.left,
                right: row_combo.right,
                goal: row_combo.goal,
              }),
              _ => None,
            })
            .collect(),
        };
        self.item_wrappers.insert(id, wrapper);
        (
          InferOut::new(constraints, Ast::Item(id, item_id)),
          ty,
        )
      },
    }
  }

  pub(crate) fn check(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>, ty: Type) -> InferOut {
    match (ast, ty) {
      (Ast::Int(id, i), Type::Int) => InferOut::new(vec![], Ast::Int(id, i)),
      (Ast::Fun(id, arg, body), Type::Fun(arg_ty, ret_ty)) => {
        let env = env.update(arg, *arg_ty.clone());
        self
          .check(env, *body, *ret_ty)
          .with_typed_ast(|body| Ast::fun(id, TypedVar(arg, *arg_ty), body))
      }
      (Ast::Label(id, ast_lbl, term), Type::Label(ty_lbl, ty)) if ast_lbl == ty_lbl => self
        .check(env, *term, *ty)
        .with_typed_ast(|term| Ast::label(id, ast_lbl, term)),
      (Ast::Unlabel(id, term, lbl), ty) => self
        .check(env, *term, Type::label(lbl.clone(), ty))
        .with_typed_ast(|term| Ast::unlabel(id, term, lbl)),
      (ast @ Ast::Concat(_, _, _), Type::Label(lbl, ty))
      | (ast @ Ast::Project(_, _, _), Type::Label(lbl, ty)) => {
        // Cast a singleton row into a product
        self.check(env, ast, Type::Prod(Row::single(lbl, *ty)))
      }
      (ast @ Ast::Branch(_, _, _), Type::Label(lbl, ty))
      | (ast @ Ast::Inject(_, _, _), Type::Label(lbl, ty)) => {
        // Cast a singleton row into a sum
        self.check(env, ast, Type::Sum(Row::single(lbl, *ty)))
      }
      (Ast::Concat(id, left, right), Type::Prod(goal_row)) => {
        let left_row = Row::Unifier(self.fresh_row_var());
        let right_row = Row::Unifier(self.fresh_row_var());

        let left_out = self.check(env.clone(), *left, Type::Prod(left_row.clone()));
        let right_out = self.check(env, *right, Type::Prod(right_row.clone()));

        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        let row_comb = RowCombination {
          left: left_row,
          right: right_row,
          goal: goal_row,
        };
        constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);

        InferOut {
          constraints,
          typed_ast: Ast::concat(id, left_out.typed_ast, right_out.typed_ast),
        }
      }
      (Ast::Project(id, dir, goal), Type::Prod(sub_row)) => {
        let goal_row = Row::Unifier(self.fresh_row_var());

        let (left, right) = match dir {
          Direction::Left => (sub_row, Row::Unifier(self.fresh_row_var())),
          Direction::Right => (Row::Unifier(self.fresh_row_var()), sub_row),
        };

        let mut out = self.check(env, *goal, Type::Prod(goal_row.clone()));
        let row_comb = RowCombination {
          left,
          right,
          goal: goal_row,
        };
        out.constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);

        out.with_typed_ast(|ast| Ast::project(id, dir, ast))
      }
      (Ast::Branch(id, left_ast, right_ast), Type::Fun(arg_ty, ret_ty)) => {
        let mut constraints = vec![];
        let goal = match arg_ty.deref() {
          Type::Sum(goal) => goal.clone(),
          _ => {
            let goal = self.fresh_row_var();
            constraints.push(Constraint::TypeEqual(
              id,
              *arg_ty,
              Type::Sum(Row::Unifier(goal)),
            ));
            Row::Unifier(goal)
          }
        };
        let left = Row::Unifier(self.fresh_row_var());
        let right = Row::Unifier(self.fresh_row_var());

        let left_out = self.check(
          env.clone(),
          *left_ast,
          Type::fun(Type::Sum(left.clone()), ret_ty.deref().clone()),
        );
        let right_out = self.check(
          env,
          *right_ast,
          Type::fun(Type::Sum(right.clone()), ret_ty.deref().clone()),
        );

        constraints.extend(left_out.constraints);
        constraints.extend(right_out.constraints);
        let row_comb = RowCombination { left, right, goal };
        constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        self.row_to_ev.insert(id, row_comb);
        self.branch_to_ret_ty.insert(id, *ret_ty);

        InferOut {
          constraints,
          typed_ast: Ast::branch(
              id,
              left_out.typed_ast, 
              right_out.typed_ast),
        }
      }
      (Ast::Inject(id, dir, value), Type::Sum(goal)) => {
        let sub_row = self.fresh_row_var();
        let mut out = self.check(env, *value, Type::Sum(Row::Unifier(sub_row)));
        let (left, right) = match dir {
          Direction::Left => (sub_row, self.fresh_row_var()),
          Direction::Right => (self.fresh_row_var(), sub_row),
        };
        let row_comb = RowCombination {
          left: Row::Unifier(left),
          right: Row::Unifier(right),
          goal,
        };
        out.constraints.push(Constraint::RowCombine(id, row_comb.clone()));
        out.with_typed_ast(|ast| Ast::inject(id, dir, ast))
      }
      (ast, expected_ty) => {
        let id = ast.id();
        let (mut out, actual_ty) = self.infer(env, ast);
        out
          .constraints
          .push(Constraint::TypeEqual(id, expected_ty, actual_ty));
        out
      }
    }
  }
}
