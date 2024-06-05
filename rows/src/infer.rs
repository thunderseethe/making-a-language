use std::ops::Deref;

use crate::ast::{Ast, Direction, TypedVar, Var};
use crate::ty::row_style::RowStyle;
use crate::ty::{Data, Row, RowCombination, RowVar, Type, TypeVar};
use crate::{Constraint, TypeInference};

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

#[derive(Clone)]
pub struct TypeAndEff {
  pub ty: Type,
  pub eff: Row,
}

impl TypeAndEff {
  pub fn new(ty: Type, eff: Row) -> Self {
    Self { ty, eff }
  }

  pub fn map_type(self, op: impl FnOnce(Type) -> Type) -> Self {
    Self {
      ty: op(self.ty),
      ..self
    }
  }
}

/// Constraint generation
impl TypeInference {
  /// Create a unique type variable
  pub(crate) fn fresh_ty_var(&mut self) -> TypeVar {
    self.unification_table.new_key(None)
  }

  /// Create a unique row variable
  pub(crate) fn fresh_row_var(&mut self) -> RowVar {
    self.row_unification_table.new_key(None)
  }

  /// Create a type and effect with an open effect row
  fn with_open_eff(&mut self, ty: Type) -> TypeAndEff {
    let eff = self.fresh_row_var();
    TypeAndEff::new(ty, Row::Open(eff))
  }

  /// Create a row combination with fresh row variables
  fn fresh_row_combination<R: RowStyle>(&mut self) -> RowCombination<R> {
    RowCombination::<R>::new(
      Row::Open(self.fresh_row_var()),
      Row::Open(self.fresh_row_var()),
      Row::Open(self.fresh_row_var()),
    )
  }

  /// Infer type of `ast` Returns a list of constraints that need to be true and the type `ast` will have if
  /// constraints hold.
  pub(crate) fn infer(
    &mut self,
    env: im::HashMap<Var, Type>,
    ast: Ast<Var>,
  ) -> (InferOut, TypeAndEff) {
    match ast {
      Ast::Unit => (
        InferOut::new(vec![], Ast::Unit),
        self.with_open_eff(Type::unit()),
      ),
      Ast::Int(i) => (
        InferOut::new(vec![], Ast::Int(i)),
        self.with_open_eff(Type::Int),
      ),
      Ast::Var(v) => {
        let ty = &env[&v];
        (
          InferOut::new(vec![], Ast::Var(TypedVar(v, ty.clone()))),
          self.with_open_eff(ty.clone()),
        )
      }
      Ast::Fun(arg, body) => {
        let arg_ty_var = self.fresh_ty_var();
        let env = env.update(arg, Type::Var(arg_ty_var));
        let (body_out, body_tyeff) = self.infer(env, *body);
        (
          InferOut {
            typed_ast: Ast::fun(TypedVar(arg, Type::Var(arg_ty_var)), body_out.typed_ast),
            ..body_out
          },
          body_tyeff.map_type(|body_ty| Type::fun(Type::Var(arg_ty_var), body_ty)),
        )
      }
      Ast::App(fun, arg) => {
        let (arg_out, arg_tyeff) = self.infer(env.clone(), *arg);

        let ret_ty = Type::Var(self.fresh_ty_var());
        let fun_tyeff = arg_tyeff.map_type(|arg_ty| Type::fun(arg_ty, ret_ty.clone()));

        let fun_out = self.check(env, *fun, fun_tyeff.clone());

        (
          InferOut::new(
            arg_out
              .constraints
              .into_iter()
              .chain(fun_out.constraints)
              .collect(),
            Ast::app(fun_out.typed_ast, arg_out.typed_ast),
          ),
          fun_tyeff.map_type(|_| ret_ty),
        )
      }
      // Labeling
      Ast::Label(label, value) => {
        let (out, value_tyeff) = self.infer(env, *value);
        (
          out.with_typed_ast(|ast| Ast::label(label.clone(), ast)),
          value_tyeff.map_type(|ty| Type::label(label, ty)),
        )
      }
      Ast::Unlabel(value, label) => {
        let value_var = self.fresh_ty_var();
        let value_eff = Row::Open(self.fresh_row_var());
        let expected = TypeAndEff::new(Type::label(label, Type::Var(value_var)), value_eff.clone());
        (
          self.check(env, *value, expected),
          TypeAndEff::new(Type::Var(value_var), value_eff),
        )
      }
      // Products
      Ast::Concat(left, right) => {
        let row_comb = self.fresh_row_combination::<Data>();
        let out_eff = Row::Open(self.fresh_row_var());

        // Concat combines two smaller rows into a larger row.
        // To check this we check that our inputs have the types of our smaller rows left
        // and right.
        let left_out = self.check(
          env.clone(),
          *left,
          TypeAndEff::new(Type::Prod(row_comb.left.clone()), out_eff.clone()),
        );
        let right_out = self.check(
          env,
          *right,
          TypeAndEff::new(Type::Prod(row_comb.right.clone()), out_eff.clone()),
        );

        // If they do, then our output type is our big row goal
        let out_ty = Type::Prod(row_comb.goal.clone());
        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        // Add a new constraint for our row combination to solve concat
        constraints.push(Constraint::DataCombo(row_comb));

        (
          InferOut {
            constraints,
            typed_ast: Ast::concat(left_out.typed_ast, right_out.typed_ast),
          },
          TypeAndEff::new(out_ty, out_eff),
        )
      }
      Ast::Project(dir, goal) => {
        let row_comb = self.fresh_row_combination::<Data>();
        let out_eff = Row::Open(self.fresh_row_var());
        // Based on the direction of our projection,
        // our output row is either left or right
        let sub_row = match dir {
          Direction::Left => row_comb.left.clone(),
          Direction::Right => row_comb.right.clone(),
        };
        // Project transforms a row into a subset of its fields, so we check our goal ast
        // node against our goal row (not our sub_row)
        let mut out = self.check(
          env,
          *goal,
          TypeAndEff::new(Type::Prod(row_comb.goal.clone()), out_eff.clone()),
        );
        // Add our row combination constraint to solve our projection
        out.constraints.push(Constraint::DataCombo(row_comb));
        (
          out.with_typed_ast(|ast| Ast::project(dir, ast)),
          // Our sub row is the output type of the projection
          TypeAndEff::new(Type::Prod(sub_row), out_eff),
        )
      }
      // Sums
      Ast::Branch(left, right) => {
        let row_comb = self.fresh_row_combination::<Data>();
        let ret_ty = self.fresh_ty_var();

        let out_eff = Row::Open(self.fresh_row_var());
        // Branch expects it's two inputs to be handling functions
        // with type: <sum> -> a
        // So we check that our left and right AST both have handler function types that
        // agree on return type
        let left_out = self.check(
          env.clone(),
          *left,
          TypeAndEff::new(
            Type::fun(Type::Sum(row_comb.left.clone()), Type::Var(ret_ty)),
            out_eff.clone(),
          ),
        );
        let right_out = self.check(
          env,
          *right,
          TypeAndEff::new(
            Type::fun(Type::Sum(row_comb.right.clone()), Type::Var(ret_ty)),
            out_eff.clone(),
          ),
        );

        // If they do the overall type of our Branch node is a function from our goal row
        // sum type to our return type
        let out_ty = Type::fun(Type::Sum(row_comb.goal.clone()), Type::Var(ret_ty));
        // Collect all our constraints for our final output
        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        constraints.push(Constraint::DataCombo(row_comb));

        (
          InferOut {
            constraints,
            typed_ast: Ast::branch(left_out.typed_ast, right_out.typed_ast),
          },
          TypeAndEff::new(out_ty, out_eff),
        )
      }
      Ast::Inject(dir, value) => {
        let row_comb = self.fresh_row_combination::<Data>();
        // Like project, inject works in terms of sub rows and goal rows.
        // But inject is _injecting_ a smaller row into a bigger row.
        let sub_row = match dir {
          Direction::Left => row_comb.left.clone(),
          Direction::Right => row_comb.right.clone(),
        };

        let out_eff = Row::Open(self.fresh_row_var());
        let out_ty = Type::Sum(row_comb.goal.clone());
        // Because of this our sub row is the type of our value
        let mut out = self.check(
          env,
          *value,
          TypeAndEff::new(Type::Sum(sub_row), out_eff.clone()),
        );
        out.constraints.push(Constraint::DataCombo(row_comb));

        (
          out.with_typed_ast(|ast| Ast::inject(dir, ast)),
          // Our goal row is the type of our output
          TypeAndEff::new(out_ty, out_eff),
        )
      }
      Ast::Handle(handler, body) => {
        let ret_ty = self.fresh_ty_var();
        let out_eff = Row::Open(self.fresh_row_var());

        let (mut body_out, body_tyeff) = self.infer(env.clone(), *body);
        let ret_row = Row::single("return", Type::fun(body_tyeff.ty, Type::Var(ret_ty)));

        let eff_sig_row = self.fresh_row_var();
        let handler_row = self.fresh_row_var();

        let handler_out = self.check(
          env,
          *handler,
          TypeAndEff::new(Type::Prod(Row::Open(handler_row)), out_eff.clone()),
        );

        body_out.constraints.extend(handler_out.constraints);
        body_out
          .constraints
          .push(Constraint::DataCombo(RowCombination::new(
            ret_row,
            Row::Open(eff_sig_row),
            Row::Open(handler_row),
          )));

        let handled_eff = self.fresh_row_var();
        body_out.constraints.push(Constraint::Handles {
          handler: Row::Open(eff_sig_row),
          eff: Row::Open(handled_eff),
          ret: Type::Var(ret_ty),
        });
        let combo = Constraint::EffCombo(RowCombination::new(
            out_eff.clone(),
            Row::Open(handled_eff),
            body_tyeff.eff,
          ));
        println!("{:?}", combo);
        body_out
          .constraints
          .push(combo);

        (
          body_out.with_typed_ast(|body| Ast::handle(handler_out.typed_ast, body)),
          TypeAndEff::new(Type::Var(ret_ty), out_eff),
        )
      }
      Ast::Operation(op_name) => {
        let sig = self.effect_member_sig(op_name);

        let unused = self.fresh_row_var();
        let goal = self.fresh_row_var();

        let ret_ty = self.fresh_ty_var();
        let eff = Row::single(self.effect_name_str_of_op(op_name), Type::Var(ret_ty));

        let constr = RowCombination::new(
            Row::Open(unused),
            eff,
            Row::Open(goal),
          );
        let out = InferOut::new(
          vec![Constraint::EffCombo(constr)],
          Ast::Operation(op_name),
        );

        (out, TypeAndEff::new(sig, Row::Open(goal)))
      }
    }
  }

  fn check(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>, tyeff: TypeAndEff) -> InferOut {
    match (ast, tyeff.ty) {
      (Ast::Int(i), Type::Int) => InferOut::new(vec![], Ast::Int(i)),
      (Ast::Fun(arg, body), Type::Fun(arg_ty, ret_ty)) => {
        let env = env.update(arg, *arg_ty);
        self.check(env, *body, TypeAndEff::new(*ret_ty, tyeff.eff))
      }
      (Ast::Label(ast_lbl, term), Type::Label(ty_lbl, ty)) if ast_lbl == ty_lbl => {
        self.check(env, *term, TypeAndEff::new(*ty, tyeff.eff))
      }
      (Ast::Unlabel(term, lbl), ty) => {
        self.check(env, *term, TypeAndEff::new(Type::label(lbl, ty), tyeff.eff))
      }
      (ast @ Ast::Concat(_, _), Type::Label(lbl, ty))
      | (ast @ Ast::Project(_, _), Type::Label(lbl, ty)) => {
        // Cast a singleton row into a product
        self.check(
          env,
          ast,
          TypeAndEff::new(Type::Prod(Row::single(lbl, *ty)), tyeff.eff),
        )
      }
      (ast @ Ast::Branch(_, _), Type::Label(lbl, ty))
      | (ast @ Ast::Inject(_, _), Type::Label(lbl, ty)) => {
        // Cast a singleton row into a sum
        self.check(
          env,
          ast,
          TypeAndEff::new(Type::Sum(Row::single(lbl, *ty)), tyeff.eff),
        )
      }
      (Ast::Concat(left, right), Type::Prod(goal_row)) => {
        let left_row = Row::Open(self.fresh_row_var());
        let right_row = Row::Open(self.fresh_row_var());

        let left_out = self.check(
          env.clone(),
          *left,
          TypeAndEff::new(Type::Prod(left_row.clone()), tyeff.eff.clone()),
        );
        let right_out = self.check(
          env,
          *right,
          TypeAndEff::new(Type::Prod(right_row.clone()), tyeff.eff),
        );

        let mut constraints = left_out.constraints;
        constraints.extend(right_out.constraints);
        constraints.push(Constraint::DataCombo(RowCombination::new(
          left_row, right_row, goal_row,
        )));

        InferOut {
          constraints,
          typed_ast: Ast::concat(left_out.typed_ast, right_out.typed_ast),
        }
      }
      (Ast::Project(dir, goal), Type::Prod(sub_row)) => {
        let goal_row = Row::Open(self.fresh_row_var());

        let (left, right) = match dir {
          Direction::Left => (sub_row, Row::Open(self.fresh_row_var())),
          Direction::Right => (Row::Open(self.fresh_row_var()), sub_row),
        };

        let mut out = self.check(
          env,
          *goal,
          TypeAndEff::new(Type::Prod(goal_row.clone()), tyeff.eff),
        );
        out
          .constraints
          .push(Constraint::DataCombo(RowCombination::new(
            left, right, goal_row,
          )));

        out.with_typed_ast(|ast| Ast::project(dir, ast))
      }
      (Ast::Branch(left_ast, right_ast), Type::Fun(arg_ty, ret_ty)) => {
        let mut constraints = vec![];
        let goal = match arg_ty.deref() {
          Type::Sum(goal) => goal.clone(),
          _ => {
            let goal = self.fresh_row_var();
            constraints.push(Constraint::TypeEqual(*arg_ty, Type::Sum(Row::Open(goal))));
            Row::Open(goal)
          }
        };
        let left = Row::Open(self.fresh_row_var());
        let right = Row::Open(self.fresh_row_var());

        let left_out = self.check(
          env.clone(),
          *left_ast,
          TypeAndEff::new(
            Type::fun(Type::Sum(left.clone()), ret_ty.deref().clone()),
            tyeff.eff.clone(),
          ),
        );
        let right_out = self.check(
          env,
          *right_ast,
          TypeAndEff::new(Type::fun(Type::Sum(right.clone()), *ret_ty), tyeff.eff),
        );

        constraints.extend(left_out.constraints);
        constraints.extend(right_out.constraints);
        constraints.push(Constraint::DataCombo(RowCombination::new(
          left, right, goal,
        )));

        InferOut {
          constraints,
          typed_ast: Ast::branch(left_out.typed_ast, right_out.typed_ast),
        }
      }
      (Ast::Inject(dir, value), Type::Sum(goal)) => {
        let sub_row = self.fresh_row_var();
        let mut out = self.check(
          env,
          *value,
          TypeAndEff::new(Type::Sum(Row::Open(sub_row)), tyeff.eff),
        );
        let (left, right) = match dir {
          Direction::Left => (sub_row, self.fresh_row_var()),
          Direction::Right => (self.fresh_row_var(), sub_row),
        };
        out
          .constraints
          .push(Constraint::DataCombo(RowCombination::new(
            Row::Open(left),
            Row::Open(right),
            goal,
          )));
        out.with_typed_ast(|ast| Ast::inject(dir, ast))
      }
      (ast, expected_ty) => {
        let (mut out, actual) = self.infer(env, ast);
        out
          .constraints
          .push(Constraint::TypeEqual(expected_ty, actual.ty));
        out
          .constraints
          .push(Constraint::EffEqual(tyeff.eff, actual.eff));
        out
      }
    }
  }
}
