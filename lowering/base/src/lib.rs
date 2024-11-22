#![allow(dead_code)]
use std::collections::HashMap;
use types_base::{self as ast, Ast, TypedVar};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct Var(u32);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct TypeVar(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
enum Type {
  Int,
  Var(TypeVar),
  Fun(Box<Self>, Box<Self>),
  Forall(Box<Self>),
}

impl Type {
  fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  fn forall(body: Self) -> Self {
    Self::Forall(Box::new(body))
  }
}

#[derive(Debug, PartialEq, Eq)]
enum IR {
  Var(Var, Type),
  Int(isize),
  Fun(Var, Type, Box<IR>),
  App(Box<IR>, Box<IR>),
  TyFun(Box<IR>),
}

impl IR {
  fn fun(var: Var, ty: Type, body: Self) -> Self {
    Self::Fun(var, ty, Box::new(body))
  }

  fn app(fun: Self, arg: Self) -> Self {
    Self::App(Box::new(fun), Box::new(arg))
  }

  fn ty_fun(ir: Self) -> Self {
    Self::TyFun(Box::new(ir))
  }

  fn type_of(&self) -> Type {
    match self {
      IR::Var(_, ty) => ty.clone(),
      IR::Int(_) => Type::Int,
      IR::Fun(_, arg_ty, body) => Type::fun(arg_ty.clone(), body.type_of()),
      IR::App(fun, arg) => {
        let Type::Fun(fun_arg_ty, ret_ty) = fun.type_of() else {
          panic!("ICE: IR used non-function type as a function")
        };
        let arg_ty = arg.type_of();
        if arg_ty != *fun_arg_ty {
          panic!("ICE: Function applied to wrong argument type");
        }
        *ret_ty
      }
      IR::TyFun(body) => Type::forall(body.type_of()),
    }
  }
}

#[derive(Default)]
struct VarSupply {
  next: u32,
  cache: HashMap<ast::Var, Var>,
}

impl VarSupply {
  fn supply_for(&mut self, var: ast::Var) -> Var {
    self
      .cache
      .entry(var)
      .or_insert_with(|| {
        let ir_var = self.next;
        self.next += 1;
        Var(ir_var)
      })
      .to_owned()
  }
}

type TypeEnv = HashMap<ast::TypeVar, TypeVar>;

fn lower_ty_scheme(scheme: ast::TypeScheme) -> (Type, TypeEnv) {
  let ty_env: TypeEnv = scheme
    .unbound
    .into_iter()
    .rev()
    .enumerate()
    .map(|(i, tyvar)| (tyvar, TypeVar(i)))
    .collect();

  let lower_ty = (0..ty_env.len()).fold(lower_ty(&ty_env, scheme.ty), |ty, _| Type::forall(ty));
  (lower_ty, ty_env)
}

fn lower_ty(env: &TypeEnv, ty: ast::Type) -> Type {
  match ty {
    ast::Type::Int => Type::Int,
    ast::Type::Var(v) => Type::Var(env[&v]),
    ast::Type::Fun(arg, ret) => {
      let arg = lower_ty(env, *arg);
      let ret = lower_ty(env, *ret);
      Type::fun(arg, ret)
    }
  }
}

fn lower_ast(supply: &mut VarSupply, ty_env: &TypeEnv, ast: Ast<TypedVar>) -> IR {
  match ast {
    Ast::Var(TypedVar(var, ty)) => IR::Var(supply.supply_for(var), lower_ty(ty_env, ty)),
    Ast::Int(i) => IR::Int(i),
    Ast::Fun(TypedVar(var, ty), body) => {
      let ir_ty = lower_ty(ty_env, ty);
      let ir_var = supply.supply_for(var);
      let ir_body = lower_ast(supply, ty_env, *body);
      IR::fun(ir_var, ir_ty, ir_body)
    }
    Ast::App(fun, arg) => {
      let ir_fun = lower_ast(supply, ty_env, *fun);
      let ir_arg = lower_ast(supply, ty_env, *arg);
      IR::app(ir_fun, ir_arg)
    }
  }
}

fn lower(ast: Ast<TypedVar>, scheme: ast::TypeScheme) -> (IR, Type) {
  let mut supply = VarSupply::default();
  let (ir_ty, ty_env) = lower_ty_scheme(scheme);
  let ir = lower_ast(&mut supply, &ty_env, ast);
  let ir = (0..ty_env.len()).fold(ir, |ir, _| IR::ty_fun(ir));
  (ir, ir_ty)
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_base::{self as ast, type_infer, Ast};

  fn lower_test(ast: Ast<ast::Var>) -> (IR, Type) {
    let (ast, scheme) = type_infer(ast).expect("Type inference to succeed");
    lower(ast, scheme)
  }

  #[test]
  fn lower_int() {
    let ast = Ast::Int(3);

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir, IR::Int(3));
    // Int
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_id_fun() {
    let x = ast::Var(0);
    let ast = Ast::fun(x, Ast::Var(x));

    let (ir, ir_ty) = lower_test(ast);

    let x = Var(0);
    let a = Type::Var(TypeVar(0));
    assert_eq!(ir, IR::ty_fun(IR::fun(x, a.clone(), IR::Var(x, a))));
    // forall(fun(Var(a), Var(a)))
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_k_combinator() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let ast = Ast::fun(x, Ast::fun(y, Ast::Var(x)));

    let (ir, ir_ty) = lower_test(ast);

    let x = Var(0);
    let y = Var(1);
    let a = TypeVar(1);
    let b = TypeVar(0);
    assert_eq!(
      ir,
      IR::ty_fun(IR::ty_fun(IR::fun(
        x,
        Type::Var(a),
        IR::fun(y, Type::Var(b), IR::Var(x, Type::Var(a)))
      )))
    );
    // forall(forall(fun(Var(a), fun(Var(b), Var(a)))))
    assert_eq!(ir_ty, ir.type_of());
  }

  
  #[test]
  fn lower_s_combinator() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let z = ast::Var(2);
    let ast = Ast::fun(
      x,
      Ast::fun(
        y,
        Ast::fun(
          z,
          Ast::app(
            Ast::app(Ast::Var(x), Ast::Var(z)),
            Ast::app(Ast::Var(y), Ast::Var(z)),
          ),
        ),
      ),
    );

    let (ir, ir_ty) = lower_test(ast);

    let x = Var(0);
    let y = Var(1);
    let z = Var(2);
    let a = TypeVar(2);
    let b = TypeVar(1);
    let c = TypeVar(0);
    let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
    let y_ty = Type::fun(Type::Var(a), Type::Var(b));
    let z_ty = Type::Var(a);
    assert_eq!(ir, 
        IR::ty_fun(IR::ty_fun(IR::ty_fun(
          IR::fun(x, x_ty.clone(), IR::fun(y, y_ty.clone(), IR::fun(z, z_ty.clone(), 
            IR::app(
              IR::app(IR::Var(x, x_ty), IR::Var(z, z_ty.clone())), 
              IR::app(IR::Var(y, y_ty), IR::Var(z, z_ty)))))))))); 
    // forall(forall(forall(fun(fun(Var(a), fun(Var(b), Var(c))), fun(fun(Var(a), Var(b)), fun(Var(a), Var(c)))))))
    assert_eq!(ir_ty, ir.type_of());
  }
}
