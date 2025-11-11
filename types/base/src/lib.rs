#![allow(dead_code)]
use std::collections::BTreeSet;

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};

/// Extra utility methods for working with our AST. These are used to make constructing ASTs in
/// tests easier.
pub mod builder;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct Var(pub usize);

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypedVar(pub Var, pub Type);

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Copy, Hash)]
pub struct NodeId(pub u32);

/// Our Abstract syntax tree
/// The lambda calculus + integer literals.
#[derive(Debug, Eq, Clone)]
pub enum Ast<V> {
  /// A local variable
  Var(NodeId, V),
  /// An integer literal
  Int(NodeId, i32),
  /// A function literal (lambda, closure).
  Fun(NodeId, V, Box<Ast<V>>),
  /// Function application
  App(NodeId, Box<Ast<V>>, Box<Ast<V>>),
  /// Typed hole.
  Hole(NodeId, V),
}

impl<V: PartialEq> PartialEq for Ast<V> {
  fn eq(&self, other: &Self) -> bool {
    // Ignore NodeID for equality.
    match (self, other) {
      (Self::Var(_, a), Self::Var(_, b)) => a == b,
      (Self::Int(_, a), Self::Int(_, b)) => a == b,
      (Self::Fun(_, a_var, a_body), Self::Fun(_, b_var, b_body)) => {
        a_var == b_var && a_body == b_body
      }
      (Self::App(_, a_fun, a_arg), Self::App(_, b_fun, b_arg)) => a_fun == b_fun && a_arg == b_arg,
      (_, _) => false,
    }
  }
}

impl<V> Ast<V> {
  pub fn id(&self) -> NodeId {
    match self {
      Ast::Var(node_id, _)
      | Ast::Int(node_id, _)
      | Ast::Fun(node_id, _, _)
      | Ast::App(node_id, _, _)
      | Ast::Hole(node_id, _) => *node_id,
    }
  }

  pub fn parents_of(&self, id: NodeId) -> Option<Vec<&Self>> {
    match self {
      Ast::Var(_, _) | Ast::Int(_, _) | Ast::Hole(_, _) => None,
      Ast::App(_, fun, arg) => {
        if id == fun.id() || id == arg.id() {
          return Some(vec![self]);
        }
        fun
          .parents_of(id)
          .or_else(|| arg.parents_of(id))
          .map(|mut parents| {
            parents.push(self);
            parents
          })
      }
      Ast::Fun(_, _, body) => {
        if id == body.id() {
          return Some(vec![self]);
        }
        body.parents_of(id).map(|mut parents| {
          parents.push(self);
          parents
        })
      }
    }
  }

  pub fn parent_of(&self, id: NodeId) -> Option<&Self> {
    // The first element of `parents_of` will be the nearest parent to `id`
    self
      .parents_of(id)
      .and_then(|parents| parents.into_iter().next())
  }

  pub fn fun(node_id: NodeId, arg: V, body: Self) -> Self {
    Self::Fun(node_id, arg, Box::new(body))
  }

  pub fn app(node_id: NodeId, fun: Self, arg: Self) -> Self {
    Self::App(node_id, Box::new(fun), Box::new(arg))
  }
}

/// Our type
/// Each AST node in our input will be annotated by a value of `Type`
/// after type inference succeeeds.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
  /// Type of integers
  Int,
  /// A type variable, stands for a value of Type
  Var(TypeVar),
  /// A function type
  Fun(Box<Self>, Box<Self>),
}
impl EqUnifyValue for Type {}
impl Type {
  pub fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  fn occurs_check(&self, var: TypeVar) -> Result<(), Type> {
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
        arg.occurs_check(var).map_err(|_| self.clone())?;
        ret.occurs_check(var).map_err(|_| self.clone())
      }
    }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct TypeVar(u32);
impl UnifyKey for TypeVar {
  type Value = Option<Type>;

  fn index(&self) -> u32 {
    self.0
  }

  fn from_index(u: u32) -> Self {
    Self(u)
  }

  fn tag() -> &'static str {
    "TypeVar"
  }
}

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
enum Constraint {
  // TODO: NodeId migAht be better represented by some kind of like provenance. Not sure yet.
  TypeEqual(Provenance, Type, Type),
}

#[derive(Debug)]
enum Provenance {
  // A non function type encountered a Fun ast node, causing a type mismatch.
  UnexpectedFun(NodeId),
  // An application has an ast node in function position that does not have a function type.
  AppExpectedFun(NodeId),
  // Constraint produced by subsumption.
  ExpectedUnify(NodeId),
}
impl Provenance {
  fn id(&self) -> NodeId {
    match self {
      Provenance::UnexpectedFun(node_id)
      | Provenance::AppExpectedFun(node_id)
      | Provenance::ExpectedUnify(node_id) => *node_id,
    }
  }
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
#[derive(Default)]
struct TypeInference {
  unification_table: InPlaceUnificationTable<TypeVar>,
  errors: std::collections::HashMap<NodeId, TypeError>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TypeError {
  InfiniteType {
    type_var: TypeVar,
    ty: Type,
  },
  UnexpectedFun {
    expected_ty: Type,
    fun_ty: Type,
  },
  AppExpectedFun {
    inferred_ty: Type,
    expected_fun_ty: Type,
  },
  ExpectedUnify {
    checked: Type,
    inferred: Type,
  },
}

struct GenOut {
  constraints: Vec<Constraint>,
  typed_ast: Ast<TypedVar>,
}

impl GenOut {
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
  fn fresh_ty_var(&mut self) -> TypeVar {
    self.unification_table.new_key(None)
  }

  /// Infer type of `ast`
  /// Returns a list of constraints that need to be true and the type `ast` will have if
  /// constraints hold.
  fn infer(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>) -> (GenOut, Type) {
    match ast {
      Ast::Int(id, i) => (GenOut::new(vec![], Ast::Int(id, i)), Type::Int),
      Ast::Var(id, v) => {
        let ty = &env[&v];
        (
          GenOut::new(vec![], Ast::Var(id, TypedVar(v, ty.clone()))),
          ty.clone(),
        )
      }
      Ast::Fun(id, arg, body) => {
        let arg_ty_var = self.fresh_ty_var();
        let env = env.update(arg, Type::Var(arg_ty_var));
        let (body_out, body_ty) = self.infer(env, *body);
        (
          GenOut {
            typed_ast: Ast::fun(id, TypedVar(arg, Type::Var(arg_ty_var)), body_out.typed_ast),
            ..body_out
          },
          Type::fun(Type::Var(arg_ty_var), body_ty),
        )
      }
      Ast::App(id, fun, arg) => {
        let fun_id = fun.id();
        let (fun_out, supposed_fun_ty) = self.infer(env.clone(), *fun);
        let mut constraint = fun_out.constraints;
        let (arg_ty, ret_ty) = match supposed_fun_ty {
          Type::Fun(arg, ret) => (*arg, *ret),
          ty => {
            let arg = self.fresh_ty_var();
            let ret = self.fresh_ty_var();

            constraint.push(Constraint::TypeEqual(
              Provenance::AppExpectedFun(fun_id),
              ty,
              Type::fun(Type::Var(arg), Type::Var(ret)),
            ));

            (Type::Var(arg), Type::Var(ret))
          }
        };

        let arg_out = self.check(env, *arg, arg_ty);
        constraint.extend(arg_out.constraints);
        (
          GenOut::new(
            constraint,
            Ast::app(id, fun_out.typed_ast, arg_out.typed_ast),
          ),
          ret_ty,
        )
      }
      Ast::Hole(id, v) => {
        let var = self.fresh_ty_var();
        (
          GenOut::new(vec![], Ast::Hole(id, TypedVar(v, Type::Var(var)))),
          Type::Var(var),
        )
      }
    }
  }

  fn check(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>, ty: Type) -> GenOut {
    match (ast, ty) {
      (Ast::Int(id, i), Type::Int) => GenOut::new(vec![], Ast::Int(id, i)),
      (Ast::Fun(id, arg, body), ty) => {
        let mut constraints = vec![];
        let (arg_ty, ret_ty) = match ty {
          Type::Fun(arg, ret) => (*arg, *ret),
          ty => {
            let arg = self.fresh_ty_var();
            let ret = self.fresh_ty_var();

            constraints.push(Constraint::TypeEqual(
              Provenance::UnexpectedFun(id),
              ty,
              Type::fun(Type::Var(arg), Type::Var(ret)),
            ));

            (Type::Var(arg), Type::Var(ret))
          }
        };
        let env = env.update(arg, arg_ty.clone());
        let body_out = self.check(env, *body, ret_ty);
        constraints.extend(body_out.constraints);
        GenOut {
          constraints,
          typed_ast: Ast::fun(id, TypedVar(arg, arg_ty), body_out.typed_ast),
        }
      }
      (ast, expected_ty) => {
        let id = ast.id();
        let (mut out, actual_ty) = self.infer(env, ast);
        out.constraints.push(Constraint::TypeEqual(
          Provenance::ExpectedUnify(id),
          expected_ty,
          actual_ty,
        ));
        out
      }
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnificationError {
  TypeNotEqual(Type, Type),
  InfiniteType(TypeVar, Type),
}

fn occurs_check(var: TypeVar, ty: Type) -> Result<(), Type> {
  match &ty {
    Type::Int => Ok(()),
    Type::Var(v) => {
      if *v == var {
        Err(Type::Var(*v))
      } else {
        Ok(())
      }
    }
    Type::Fun(arg, ret) => {
      occurs_check(var, *arg.clone()).map_err(|_| ty.clone())?;
      occurs_check(var, *ret.clone()).map_err(|_| ty.clone())
    }
  }
}

/// Constraint solving
impl TypeInference {
  fn unification(&mut self, constraints: Vec<Constraint>) {
    for constr in constraints {
      match constr {
        Constraint::TypeEqual(provenance, left, right) => {
          if let Err(kind) = self.unify_ty_ty(left, right) {
            let (node_id, mark) = match kind {
              UnificationError::InfiniteType(type_var, ty) => {
                (provenance.id(), TypeError::InfiniteType { type_var, ty })
              }
              UnificationError::TypeNotEqual(left, right) => match provenance {
                Provenance::UnexpectedFun(node_id) => (
                  node_id,
                  TypeError::UnexpectedFun {
                    expected_ty: left,
                    fun_ty: right,
                  },
                ),
                Provenance::AppExpectedFun(node_id) => (
                  node_id,
                  TypeError::AppExpectedFun {
                    inferred_ty: left,
                    expected_fun_ty: right,
                  },
                ),
                Provenance::ExpectedUnify(node_id) => (
                  node_id,
                  TypeError::ExpectedUnify {
                    checked: left,
                    inferred: right,
                  },
                ),
              },
            };
            self.errors.insert(node_id, mark);
          }
        }
      }
    }
  }

  fn normalize_ty(&mut self, ty: Type) -> Type {
    match ty {
      Type::Int => Type::Int,
      Type::Fun(arg, ret) => {
        let arg = self.normalize_ty(*arg);
        let ret = self.normalize_ty(*ret);
        Type::fun(arg, ret)
      }
      Type::Var(v) => match self.unification_table.probe_value(v) {
        Some(ty) => self.normalize_ty(ty),
        None => Type::Var(self.unification_table.find(v)),
      },
    }
  }

  fn unify_ty_ty(&mut self, unnorm_left: Type, unnorm_right: Type) -> Result<(), UnificationError> {
    let left = self.normalize_ty(unnorm_left);
    let right = self.normalize_ty(unnorm_right);
    match (left, right) {
      (Type::Int, Type::Int) => Ok(()),
      (Type::Fun(a_arg, a_ret), Type::Fun(b_arg, b_ret)) => {
        self
          .unify_ty_ty(*a_arg.clone(), *b_arg.clone())
          .map_err(|kind| match kind {
            UnificationError::TypeNotEqual(a_arg, b_arg) => UnificationError::TypeNotEqual(
              Type::fun(a_arg, *a_ret.clone()),
              Type::fun(b_arg, *b_ret.clone()),
            ),
            kind => kind,
          })?;
        self.unify_ty_ty(*a_ret, *b_ret).map_err(|kind| match kind {
          UnificationError::TypeNotEqual(a_ret, b_ret) => {
            UnificationError::TypeNotEqual(Type::fun(*a_arg, a_ret), Type::fun(*b_arg, b_ret))
          }
          kind => kind,
        })
      }
      (Type::Var(a), Type::Var(b)) => self
        .unification_table
        .unify_var_var(a, b)
        .map_err(|(l, r)| UnificationError::TypeNotEqual(l, r)),
      (Type::Var(v), ty) | (ty, Type::Var(v)) => {
        ty.occurs_check(v)
          .map_err(|ty| UnificationError::InfiniteType(v, ty))?;
        self
          .unification_table
          .unify_var_value(v, Some(ty))
          .map_err(|(l, r)| UnificationError::TypeNotEqual(l, r))
      }
      (left, right) => Err(UnificationError::TypeNotEqual(left, right)),
    }
  }
}

impl TypeInference {
  fn substitute(&mut self, ty: Type) -> (BTreeSet<TypeVar>, Type) {
    match ty {
      Type::Int => (BTreeSet::new(), Type::Int),
      Type::Var(v) => {
        let root = self.unification_table.find(v);
        match self.unification_table.probe_value(root) {
          Some(ty) => self.substitute(ty),
          None => {
            let mut unbound = BTreeSet::new();
            unbound.insert(root);
            (unbound, Type::Var(root))
          }
        }
      }
      Type::Fun(arg, ret) => {
        let (mut arg_unbound, arg) = self.substitute(*arg);
        let (ret_unbound, ret) = self.substitute(*ret);
        arg_unbound.extend(ret_unbound);
        (arg_unbound, Type::fun(arg, ret))
      }
    }
  }

  fn substitute_ast(&mut self, ast: Ast<TypedVar>) -> (BTreeSet<TypeVar>, Ast<TypedVar>) {
    match ast {
      Ast::Var(id, v) => {
        let (unbound, ty) = self.substitute(v.1);
        (unbound, Ast::Var(id, TypedVar(v.0, ty)))
      }
      Ast::Int(id, i) => (BTreeSet::new(), Ast::Int(id, i)),
      Ast::Hole(id, v) => {
        let (unbound, ty) = self.substitute(v.1);
        (unbound, Ast::Hole(id, TypedVar(v.0, ty)))
      }
      Ast::Fun(id, arg, body) => {
        let (mut unbound, ty) = self.substitute(arg.1);
        let arg = TypedVar(arg.0, ty);

        let (unbound_body, body) = self.substitute_ast(*body);
        unbound.extend(unbound_body);

        (unbound, Ast::fun(id, arg, body))
      }
      Ast::App(id, fun, arg) => {
        let (mut unbound_fun, fun) = self.substitute_ast(*fun);
        let (unbound_arg, arg) = self.substitute_ast(*arg);
        unbound_fun.extend(unbound_arg);
        (unbound_fun, Ast::app(id, fun, arg))
      }
    }
  }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeScheme {
  pub unbound: BTreeSet<TypeVar>,
  pub ty: Type,
}

pub struct TypeInferOut {
  pub ast: Ast<TypedVar>,
  pub scheme: TypeScheme,
  pub errors: std::collections::HashMap<NodeId, TypeError>,
}

pub fn type_infer(ast: Ast<Var>) -> TypeInferOut {
  let mut ctx = TypeInference {
    unification_table: InPlaceUnificationTable::default(),
    errors: Default::default(),
  };

  // Constraint generation
  let (out, ty) = ctx.infer(im::HashMap::default(), ast);

  // Constraint solving
  ctx.unification(out.constraints);

  // Apply our substition to our inferred types
  let (mut unbound, ty) = ctx.substitute(ty);
  let (unbound_ast, typed_ast) = ctx.substitute_ast(out.typed_ast);
  unbound.extend(unbound_ast);

  // Return our typed ast and it's type scheme
  TypeInferOut {
    ast: typed_ast,
    scheme: TypeScheme { unbound, ty },
    errors: ctx.errors,
  }
}

fn main() {
  println!("Hello, world!");
}

#[cfg(test)]
mod tests {

  use crate::builder::make_vars;

  use self::builder::AstBuilder;

  use super::*;

  macro_rules! set {
    ($($ele:expr),*) => {{
        let mut tmp = BTreeSet::new();
        $(tmp.insert($ele);)*
        tmp
    }};
  }

  #[test]
  fn infers_int() {
    let b = AstBuilder::default();
    let ast = b.int(3);

    let ty_chk = type_infer(ast);
    assert_eq!(ty_chk.ast, Ast::Int(NodeId(0), 3));
    assert_eq!(ty_chk.scheme.ty, Type::Int);
  }

  #[test]
  fn infers_id_fun() {
    let x = Var(0);
    let b = AstBuilder::default();
    let ast = b.fun(x, b.var(x));

    let ty_chk = type_infer(ast);

    let a = TypeVar(0);
    let typed_x = TypedVar(x, Type::Var(a));
    assert_eq!(
      ty_chk.ast,
      Ast::fun(NodeId(1), typed_x.clone(), Ast::Var(NodeId(0), typed_x))
    );
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound: set![a],
        ty: Type::fun(Type::Var(a), Type::Var(a)),
      }
    )
  }

  #[test]
  fn infers_k_combinator() {
    let x = Var(0);
    let y = Var(1);
    let b = AstBuilder::default();
    let ast = b.funs([x, y], b.var(x));

    let ty_chk = type_infer(ast);

    let a = TypeVar(0);
    let b = TypeVar(1);
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound: set![a, b],
        ty: Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(a))),
      }
    );
  }

  #[test]
  fn infers_s_combinator() {
    let x = Var(0);
    let y = Var(1);
    let z = Var(2);
    let b = AstBuilder::default();
    let ast = b.funs(
      [x, y, z],
      b.app(b.app(b.var(x), b.var(z)), b.app(b.var(y), b.var(z))),
    );

    let ty_chk = type_infer(ast);

    let a = TypeVar(2);
    let b = TypeVar(8);
    let c = TypeVar(6);
    let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
    let y_ty = Type::fun(Type::Var(a), Type::Var(b));
    assert_eq!(
      ty_chk.scheme,
      TypeScheme {
        unbound: set![a, b, c],
        ty: Type::fun(x_ty, Type::fun(y_ty, Type::fun(Type::Var(a), Type::Var(c)))),
      }
    )
  }

  #[test]
  fn type_infer_fails() {
    let x = Var(0);
    let b = AstBuilder::default();
    let ast = b.locals([(x, b.int(1))], b.app(b.var(x), b.int(3)));

    let ty_chk = type_infer(ast);

    assert_eq!(
      ty_chk.errors[&NodeId(0)],
      TypeError::ExpectedUnify {
        checked: Type::fun(Type::Int, Type::Var(TypeVar(2))),
        inferred: Type::Int
      }
    );
  }

  #[test]
  fn type_infer_fails_with_meaningful_error() {
    let b = AstBuilder::default();
    let [f, x, y] = make_vars();
    let ast = b.app(
      b.fun(y, b.apps(b.var(y), [b.int(3), b.int(4)])),
      b.funs([f, x], b.app(b.var(f), b.var(x))),
    );

    let ty_chk = type_infer(ast);

    let a = TypeVar(9);
    let b = TypeVar(10);
    assert_eq!(
      ty_chk.errors[&NodeId(6)],
      TypeError::AppExpectedFun {
        inferred_ty: Type::Int,
        expected_fun_ty: Type::fun(Type::Var(a), Type::Var(b))
      },
    );
  }
}
