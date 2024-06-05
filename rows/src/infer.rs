use std::ops::Deref;

use crate::ast::{
  Ast, Direction, TypedVar,
  Var,
};
use crate::ty::{
  Row, RowCombination,
  RowVar, Type, TypeVar,
};
use crate::{
  Constraint, TypeInference,
};

pub struct InferOut {
  pub constraints:
    Vec<Constraint>,
  pub typed_ast:
    Ast<TypedVar>,
}
impl InferOut {
  fn with_typed_ast(
    self,
    f: impl FnOnce(
      Ast<TypedVar>,
    ) -> Ast<
      TypedVar,
    >,
  ) -> Self {
    InferOut {
      constraints: self
        .constraints,
      typed_ast: f(
        self.typed_ast
      ),
    }
  }
}

impl InferOut {
  fn new(
    constraints: Vec<
      Constraint,
    >,
    typed_ast: Ast<TypedVar>,
  ) -> Self {
    Self {
      constraints,
      typed_ast,
    }
  }
}

/// Constraint generation
impl TypeInference {
  /// Create a unique type variable
  fn fresh_ty_var(
    &mut self,
  ) -> TypeVar {
    self
      .unification_table
      .new_key(None)
  }

  /// Create a unique row variable
  fn fresh_row_var(
    &mut self,
  ) -> RowVar {
    self
      .row_unification_table
      .new_key(None)
  }

  /// Create a row combination with fresh row variables
  fn fresh_row_combination(
    &mut self,
  ) -> RowCombination {
    RowCombination {
      left: Row::Open(
        self.fresh_row_var(),
      ),
      right: Row::Open(
        self.fresh_row_var(),
      ),
      goal: Row::Open(
        self.fresh_row_var(),
      ),
    }
  }

  /// Infer type of `ast`
  /// Returns a list of constraints that need to be true and the type `ast` will have if
  /// constraints hold.
  pub(crate) fn infer(
    &mut self,
    env: im::HashMap<
      Var,
      Type,
    >,
    ast: Ast<Var>,
  ) -> (InferOut, Type) {
    match ast {
      Ast::Int(i) => (
        InferOut::new(
          vec![],
          Ast::Int(i),
        ),
        Type::Int,
      ),
      Ast::Var(v) => {
        let ty = &env[&v];
        (
          InferOut::new(
            vec![],
            Ast::Var(
              TypedVar(
                v,
                ty.clone(),
              ),
            ),
          ),
          ty.clone(),
        )
      }
      Ast::Fun(arg, body) => {
        let arg_ty_var =
          self.fresh_ty_var();
        let env = env.update(
          arg,
          Type::Var(
            arg_ty_var,
          ),
        );
        let (
          body_out,
          body_ty,
        ) = self
          .infer(env, *body);
        (
        InferOut {
          typed_ast: Ast::fun(TypedVar(arg, Type::Var(arg_ty_var)), body_out.typed_ast),
          ..body_out
        },
        Type::fun(Type::Var(arg_ty_var), body_ty),
      )
      }
      Ast::App(fun, arg) => {
        let (arg_out, arg_ty) =
          self.infer(
            env.clone(),
            *arg,
          );

        let ret_ty =
          Type::Var(
            self
              .fresh_ty_var(),
          );
        let fun_ty =
          Type::fun(
            arg_ty,
            ret_ty.clone(),
          );

        let fun_out = self
          .check(
            env, *fun, fun_ty,
          );

        (
        InferOut::new(
          arg_out
            .constraints
            .into_iter()
            .chain(fun_out.constraints)
            .collect(),
          Ast::app(fun_out.typed_ast, arg_out.typed_ast),
        ),
        ret_ty,
      )
      }
      // Labeling
      Ast::Label(
        label,
        value,
      ) => {
        let (out, value_ty) =
          self.infer(
            env, *value,
          );
        (
          out.with_typed_ast(
            |ast| {
              Ast::label(
                label.clone(),
                ast,
              )
            },
          ),
          Type::label(
            label, value_ty,
          ),
        )
      }
      Ast::Unlabel(
        value,
        label,
      ) => {
        let value_var =
          self.fresh_ty_var();
        let expected_ty =
          Type::label(
            label,
            Type::Var(
              value_var,
            ),
          );
        (
          self.check(
            env,
            *value,
            expected_ty,
          ),
          Type::Var(
            value_var,
          ),
        )
      }
      // Products
      Ast::Concat(
        left,
        right,
      ) => {
        let row_comb = self.fresh_row_combination();

        // Concat combines two smaller rows into a larger row.
        // To check this we check that our inputs have the types of our smaller rows left
        // and right.
        let left_out = self
          .check(
            env.clone(),
            *left,
            Type::Prod(
              row_comb
                .left
                .clone(),
            ),
          );
        let right_out = self
          .check(
            env,
            *right,
            Type::Prod(
              row_comb
                .right
                .clone(),
            ),
          );

        // If they do, then our output type is our big row goal
        let out_ty =
          Type::Prod(
            row_comb
              .goal
              .clone(),
          );
        let mut constraints =
          left_out.constraints;
        constraints.extend(
          right_out
            .constraints,
        );
        // Add a new constraint for our row combination to solve concat
        constraints.push(Constraint::RowCombine(row_comb));

        (
          InferOut {
            constraints,
            typed_ast:
              Ast::concat(
                left_out
                  .typed_ast,
                right_out
                  .typed_ast,
              ),
          },
          out_ty,
        )
      }
      Ast::Project(
        dir,
        goal,
      ) => {
        let row_comb = self.fresh_row_combination();
        // Based on the direction of our projection,
        // our output row is either left or right
        let sub_row = match dir {
        Direction::Left => row_comb.left.clone(),
        Direction::Right => row_comb.right.clone(),
      };
        // Project transforms a row into a subset of its fields, so we check our goal ast
        // node against our goal row (not our sub_row)
        let mut out = self
          .check(
            env,
            *goal,
            Type::Prod(
              row_comb
                .goal
                .clone(),
            ),
          );
        // Add our row combination constraint to solve our projection
        out.constraints.push(Constraint::RowCombine(row_comb));
        (
          out.with_typed_ast(
            |ast| {
              Ast::project(
                dir, ast,
              )
            },
          ),
          // Our sub row is the output type of the projection
          Type::Prod(sub_row),
        )
      }
      // Sums
      Ast::Branch(
        left,
        right,
      ) => {
        let row_comb = self.fresh_row_combination();
        let ret_ty =
          self.fresh_ty_var();

        // Branch expects it's two inputs to be handling functions
        // with type: <sum> -> a
        // So we check that our left and right AST both have handler function types that
        // agree on return type
        let left_out = self
          .check(
            env.clone(),
            *left,
            Type::fun(
              Type::Sum(
                row_comb
                  .left
                  .clone(),
              ),
              Type::Var(
                ret_ty,
              ),
            ),
          );
        let right_out = self
          .check(
            env,
            *right,
            Type::fun(
              Type::Sum(
                row_comb
                  .right
                  .clone(),
              ),
              Type::Var(
                ret_ty,
              ),
            ),
          );

        // If they do the overall type of our Branch node is a function from our goal row
        // sum type to our return type
        let out_ty =
          Type::fun(
            Type::Sum(
              row_comb
                .goal
                .clone(),
            ),
            Type::Var(ret_ty),
          );
        // Collect all our constraints for our final output
        let mut constraints =
          left_out.constraints;
        constraints.extend(
          right_out
            .constraints,
        );
        constraints.push(Constraint::RowCombine(row_comb));

        (
          InferOut {
            constraints,
            typed_ast:
              Ast::branch(
                left_out
                  .typed_ast,
                right_out
                  .typed_ast,
              ),
          },
          out_ty,
        )
      }
      Ast::Inject(
        dir,
        value,
      ) => {
        let row_comb = self.fresh_row_combination();
        // Like project, inject works in terms of sub rows and goal rows.
        // But inject is _injecting_ a smaller row into a bigger row.
        let sub_row = match dir {
        Direction::Left => row_comb.left.clone(),
        Direction::Right => row_comb.right.clone(),
      };

        let out_ty =
          Type::Sum(
            row_comb
              .goal
              .clone(),
          );
        // Because of this our sub row is the type of our value
        let mut out = self
          .check(
            env,
            *value,
            Type::Sum(
              sub_row,
            ),
          );
        out.constraints.push(Constraint::RowCombine(row_comb));
        (
          out.with_typed_ast(
            |ast| {
              Ast::inject(
                dir, ast,
              )
            },
          ),
          // Our goal row is the type of our output
          out_ty,
        )
      }
    }
  }

  fn check(
    &mut self,
    env: im::HashMap<
      Var,
      Type,
    >,
    ast: Ast<Var>,
    ty: Type,
  ) -> InferOut {
    match (ast, ty) {
      (
        Ast::Int(i),
        Type::Int,
      ) => InferOut::new(
        vec![],
        Ast::Int(i),
      ),
      (
        Ast::Fun(arg, body),
        Type::Fun(
          arg_ty,
          ret_ty,
        ),
      ) => {
        let env = env.update(
          arg, *arg_ty,
        );
        self.check(
          env, *body, *ret_ty,
        )
      }
      (
        Ast::Label(
          ast_lbl,
          term,
        ),
        Type::Label(
          ty_lbl,
          ty,
        ),
      ) if ast_lbl
        == ty_lbl =>
      {
        self.check(
          env, *term, *ty,
        )
      }
      (
        Ast::Unlabel(
          term,
          lbl,
        ),
        ty,
      ) => self.check(
        env,
        *term,
        Type::label(lbl, ty),
      ),
      (
        ast @ Ast::Concat(
          _,
          _,
        ),
        Type::Label(lbl, ty),
      )
      | (
        ast @ Ast::Project(
          _,
          _,
        ),
        Type::Label(lbl, ty),
      ) => {
        // Cast a singleton row into a product
        self.check(
          env,
          ast,
          Type::Prod(
            Row::single(
              lbl, *ty,
            ),
          ),
        )
      }
      (
        ast @ Ast::Branch(
          _,
          _,
        ),
        Type::Label(lbl, ty),
      )
      | (
        ast @ Ast::Inject(
          _,
          _,
        ),
        Type::Label(lbl, ty),
      ) => {
        // Cast a singleton row into a sum
        self.check(
          env,
          ast,
          Type::Sum(
            Row::single(
              lbl, *ty,
            ),
          ),
        )
      }
      (
        Ast::Concat(
          left,
          right,
        ),
        Type::Prod(goal_row),
      ) => {
        let left_row =
          Row::Open(
            self
              .fresh_row_var(
              ),
          );
        let right_row =
          Row::Open(
            self
              .fresh_row_var(
              ),
          );

        let left_out = self
          .check(
            env.clone(),
            *left,
            Type::Prod(
              left_row
                .clone(),
            ),
          );
        let right_out = self
          .check(
            env,
            *right,
            Type::Prod(
              right_row
                .clone(),
            ),
          );

        let mut constraints =
          left_out.constraints;
        constraints.extend(
          right_out
            .constraints,
        );
        constraints.push(Constraint::RowCombine(RowCombination {
        left: left_row,
        right: right_row,
        goal: goal_row,
      }));

        InferOut {
          constraints,
          typed_ast:
            Ast::concat(
              left_out
                .typed_ast,
              right_out
                .typed_ast,
            ),
        }
      }
      (
        Ast::Project(
          dir,
          goal,
        ),
        Type::Prod(sub_row),
      ) => {
        let goal_row =
          Row::Open(
            self
              .fresh_row_var(
              ),
          );

        let (left, right) = match dir {
        Direction::Left => (sub_row, Row::Open(self.fresh_row_var())),
        Direction::Right => (Row::Open(self.fresh_row_var()), sub_row),
      };

        let mut out = self
          .check(
            env,
            *goal,
            Type::Prod(
              goal_row
                .clone(),
            ),
          );
        out.constraints.push(Constraint::RowCombine(RowCombination {
        left,
        right,
        goal: goal_row,
      }));

        out.with_typed_ast(
          |ast| {
            Ast::project(
              dir, ast,
            )
          },
        )
      }
      (
        Ast::Branch(
          left_ast,
          right_ast,
        ),
        Type::Fun(
          arg_ty,
          ret_ty,
        ),
      ) => {
        let mut constraints =
          vec![];
        let goal =
          match arg_ty.deref()
          {
            Type::Sum(
              goal,
            ) => goal.clone(),
            _ => {
              let goal = self.fresh_row_var();
              constraints.push(Constraint::TypeEqual(*arg_ty, Type::Sum(Row::Open(goal))));
              Row::Open(goal)
            }
          };
        let left = Row::Open(
          self
            .fresh_row_var(),
        );
        let right = Row::Open(
          self
            .fresh_row_var(),
        );

        let left_out = self
          .check(
            env.clone(),
            *left_ast,
            Type::fun(
              Type::Sum(
                left.clone(),
              ),
              ret_ty
                .deref()
                .clone(),
            ),
          );
        let right_out = self
          .check(
            env,
            *right_ast,
            Type::fun(
              Type::Sum(
                right.clone(),
              ),
              *ret_ty,
            ),
          );

        constraints.extend(
          left_out
            .constraints,
        );
        constraints.extend(
          right_out
            .constraints,
        );
        constraints.push(Constraint::RowCombine(RowCombination { left, right, goal }));

        InferOut {
          constraints,
          typed_ast:
            Ast::branch(
              left_out
                .typed_ast,
              right_out
                .typed_ast,
            ),
        }
      }
      (
        Ast::Inject(
          dir,
          value,
        ),
        Type::Sum(goal),
      ) => {
        let sub_row = self
          .fresh_row_var();
        let mut out = self
          .check(
            env,
            *value,
            Type::Sum(
              Row::Open(
                sub_row,
              ),
            ),
          );
        let (left, right) = match dir {
        Direction::Left => (sub_row, self.fresh_row_var()),
        Direction::Right => (self.fresh_row_var(), sub_row),
      };
        let row_comb =
          RowCombination {
            left: Row::Open(
              left,
            ),
            right: Row::Open(
              right,
            ),
            goal,
          };
        out.constraints.push(Constraint::RowCombine(row_comb));
        out.with_typed_ast(
          |ast| {
            Ast::inject(
              dir, ast,
            )
          },
        )
      }
      (ast, expected_ty) => {
        let (
          mut out,
          actual_ty,
        ) = self
          .infer(env, ast);
        out
        .constraints
        .push(Constraint::TypeEqual(expected_ty, actual_ty));
        out
      }
    }
  }
}
