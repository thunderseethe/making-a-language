#![allow(dead_code)]
use std::cmp::Ordering;
use std::collections::HashMap;
use types_base::{self as ast, Ast, TypedVar};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct VarId(usize);

#[derive(Debug, Eq, PartialEq, Clone)]
struct Var {
  id: VarId,
  ty: Type,
}

impl Var {
  fn new(id: VarId, ty: Type) -> Self {
    Self { id, ty }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct TypeVar(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
enum Kind {
  Type,
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Type {
  Int,
  Var(TypeVar),
  Fun(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
}

impl Type {
  fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  fn ty_fun(kind: Kind, body: Self) -> Self {
    Self::TyFun(kind, Box::new(body))
  }

  fn subst_internal(self, ty: Self, needle: usize) -> Self {
    match self {
      Type::Int => Type::Int,
      Type::Var(type_var) => match type_var.0.cmp(&needle) {
        Ordering::Equal => ty,
        Ordering::Less => Type::Var(type_var),
        Ordering::Greater => Type::Var(TypeVar(type_var.0 - 1)),
      },
      Type::Fun(arg, ret) => Type::fun(arg.subst(ty.clone()), ret.subst(ty)),
      Type::TyFun(kind, body) => Type::ty_fun(kind, body.subst_internal(ty, needle + 1)),
    }
  }

  fn subst(self, ty: Self) -> Self {
    self.subst_internal(ty, 0)
  }
}

#[derive(Debug, PartialEq, Eq)]
enum IR {
  Var(Var),
  Int(isize),
  Fun(Var, Box<Self>),
  App(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
  TyApp(Box<Self>, Type),
}

impl IR {
  fn fun(var: Var, body: Self) -> Self {
    Self::Fun(var, Box::new(body))
  }

  fn app(fun: Self, arg: Self) -> Self {
    Self::App(Box::new(fun), Box::new(arg))
  }

  fn ty_fun(kind: Kind, ir: Self) -> Self {
    Self::TyFun(kind, Box::new(ir))
  }

  fn type_of(&self) -> Type {
    match self {
      IR::Var(v) => v.ty.clone(),
      IR::Int(_) => Type::Int,
      IR::Fun(arg, body) => Type::fun(arg.ty.clone(), body.type_of()),
      IR::App(fun, arg) => {
        let Type::Fun(fun_arg_ty, ret_ty) = fun.type_of() else {
          panic!("ICE: IR used non-function type as a function")
        };
        if arg.type_of() != *fun_arg_ty {
          panic!("ICE: Function applied to wrong argument type");
        }
        *ret_ty
      }
      IR::TyFun(kind, body) => Type::ty_fun(*kind, body.type_of()),
      IR::TyApp(ty_fun, ty) => {
        let Type::TyFun(_, ret_ty) = ty_fun.type_of() else {
          panic!("ICE: Type applied to a non-forall IR term");
        };

        ret_ty.subst(ty.clone())
      }
    }
  }
}

#[derive(Default)]
struct VarSupply {
  next: usize,
  cache: HashMap<ast::Var, VarId>,
}

impl VarSupply {
  fn supply_for(&mut self, var: ast::Var) -> VarId {
    self
      .cache
      .entry(var)
      .or_insert_with(|| {
        let ir_var = self.next;
        self.next += 1;
        VarId(ir_var)
      })
      .to_owned()
  }
}

struct LowerTypes {
  env: HashMap<ast::TypeVar, TypeVar>,
}

impl LowerTypes {
  fn lower_ty(&self, ty: ast::Type) -> Type {
    match ty {
      ast::Type::Int => Type::Int,
      ast::Type::Var(v) => Type::Var(self.env[&v]),
      ast::Type::Fun(arg, ret) => {
        let arg = self.lower_ty(*arg);
        let ret = self.lower_ty(*ret);
        Type::fun(arg, ret)
      }
    }
  }
}

fn lower_ty_scheme(scheme: ast::TypeScheme) -> (Type, LowerTypes) {
  let ty_env = scheme
    .unbound
    .into_iter()
    .rev()
    .enumerate()
    .map(|(i, tyvar)| (tyvar, TypeVar(i)))
    .collect();

  let lower = LowerTypes { env: ty_env };
  let lower_ty = lower.lower_ty(scheme.ty);
  let bound_lower_ty = (0..lower.env.len()).fold(lower_ty, |ty, _| {
    Type::ty_fun(Kind::Type, ty)
  });
  (bound_lower_ty, lower)
}

struct LowerAst {
  supply: VarSupply,
  types: LowerTypes,
}

impl LowerAst {
  fn lower_ast(&mut self, ast: Ast<TypedVar>) -> IR {
    match ast {
      Ast::Var(TypedVar(var, ty)) => IR::Var(Var::new(
        self.supply.supply_for(var),
        self.types.lower_ty(ty),
      )),
      Ast::Int(i) => IR::Int(i),
      Ast::Fun(TypedVar(var, ty), body) => {
        let ir_ty = self.types.lower_ty(ty);
        let ir_var = self.supply.supply_for(var);
        let ir_body = self.lower_ast(*body);
        IR::fun(Var::new(ir_var, ir_ty), ir_body)
      }
      Ast::App(fun, arg) => {
        let ir_fun = self.lower_ast(*fun);
        let ir_arg = self.lower_ast(*arg);
        IR::app(ir_fun, ir_arg)
      }
    }
  }
}

fn lower(ast: Ast<TypedVar>, scheme: ast::TypeScheme) -> (IR, Type) {
  let (ir_ty, types) = lower_ty_scheme(scheme);
  let mut lower_ast = LowerAst {
    supply: VarSupply::default(),
    types,
  };
  let ir = lower_ast.lower_ast(ast);
  let bound_ir = 
    (0..lower_ast.types.env.len())
      .fold(ir, |ir, _| IR::ty_fun(Kind::Type, ir));
  (bound_ir, ir_ty)
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

    let a = Type::Var(TypeVar(0));
    let x = Var::new(VarId(0), a);
    assert_eq!(ir, IR::ty_fun(Kind::Type, IR::fun(x.clone(), IR::Var(x))));
    // forall(fun(Var(a), Var(a)))
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_k_combinator() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let ast = Ast::fun(x, Ast::fun(y, Ast::Var(x)));

    let (ir, ir_ty) = lower_test(ast);

    let a = TypeVar(1);
    let b = TypeVar(0);
    let x = Var::new(VarId(0), Type::Var(a));
    let y = Var::new(VarId(1), Type::Var(b));
    assert_eq!(
      ir,
      IR::ty_fun(
        Kind::Type,
        IR::ty_fun(Kind::Type, IR::fun(x.clone(), IR::fun(y, IR::Var(x))))
      )
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

    let a = TypeVar(2);
    let b = TypeVar(1);
    let c = TypeVar(0);
    let x = Var::new(
      VarId(0),
      Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c))),
    );
    let y = Var::new(VarId(1), Type::fun(Type::Var(a), Type::Var(b)));
    let z = Var::new(VarId(2), Type::Var(a));
    assert_eq!(
      ir,
      IR::ty_fun(
        Kind::Type,
        IR::ty_fun(
          Kind::Type,
          IR::ty_fun(
            Kind::Type,
            IR::fun(
              x.clone(),
              IR::fun(
                y.clone(),
                IR::fun(
                  z.clone(),
                  IR::app(
                    IR::app(IR::Var(x), IR::Var(z.clone())),
                    IR::app(IR::Var(y), IR::Var(z))
                  )
                )
              )
            )
          )
        )
      )
    );
    // forall(forall(forall(fun(fun(Var(a), fun(Var(b), Var(c))), fun(fun(Var(a), Var(b)), fun(Var(a), Var(c)))))))
    assert_eq!(ir_ty, ir.type_of());
  }
}
