#![allow(dead_code)]
use std::cmp::Ordering;
use std::collections::HashMap;
use types_base::{self as ast, Ast, TypedVar};

pub mod pretty;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct VarId(usize);

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct Var {
  pub id: VarId,
  pub ty: Type,
}

impl PartialOrd for Var {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Var {
  fn cmp(&self, other: &Self) -> Ordering {
    self.id.cmp(&other.id)
  }
}

impl Var {
  fn new(id: VarId, ty: Type) -> Self {
    Self { id, ty }
  }

  pub fn map_ty(self, f: impl FnOnce(Type) -> Type) -> Self {
    Self {
      ty: f(self.ty),
      ..self
    }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct TypeVar(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub enum Kind {
  Type,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
  Int,
  Var(TypeVar),
  Fun(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
}

impl TypeVar {
  fn adjust(&mut self, cutoff: usize) {
    if self.0 >= cutoff {
      self.0 += 1;
    }
  }
}

impl Type {
  fn adjust(&mut self, cutoff: usize) {
    match self {
      Type::Int => {}
      Type::Var(type_var) => type_var.adjust(cutoff),
      Type::Fun(arg, ret) => {
        arg.adjust(cutoff);
        ret.adjust(cutoff);
      }
      Type::TyFun(_, body) => {
        body.adjust(cutoff + 1);
      }
    }
  }

  fn shift(&mut self) {
    self.adjust(0);
  }

  fn shifted(mut self) -> Self {
    self.shift();
    self
  }
}

#[derive(Clone)]
enum Subst {
  TyPayload(Type),
}
impl Subst {
  fn shift(&mut self) {
    match self {
      Subst::TyPayload(ty) => ty.shift(),
    }
  }

  fn shifted(mut self) -> Self {
    self.shift();
    self
  }

  fn subst_ty_var(self) -> Type {
    match self {
      Subst::TyPayload(ty) => ty,
    }
  }

  fn subst_ty(self, haystack: Type, needle: usize) -> Type {
    match haystack {
      Type::Int => Type::Int,
      Type::Var(type_var) => match type_var.0.cmp(&needle) {
        Ordering::Equal => self.subst_ty_var(),
        Ordering::Less => Type::Var(type_var),
        Ordering::Greater => Type::Var(TypeVar(type_var.0 - 1)),
      },
      Type::Fun(arg, ret) => Type::fun(
        self.clone().subst_ty(*arg, needle),
        self.subst_ty(*ret, needle),
      ),
      Type::TyFun(kind, body) => Type::ty_fun(kind, self.shifted().subst_ty(*body, needle + 1)),
    }
  }
}

impl Type {
  fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  fn ty_fun(kind: Kind, body: Self) -> Self {
    Self::TyFun(kind, Box::new(body))
  }

  pub fn subst_ty(self, ty: Self) -> Self {
    Subst::TyPayload(ty).subst_ty(self, 0)
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IR {
  Var(Var),
  Int(i32),
  Fun(Var, Box<Self>),
  App(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
  TyApp(Box<Self>, Type),
  Local(Var, Box<Self>, Box<Self>),
}

impl IR {
  pub fn fun(var: Var, body: Self) -> Self {
    Self::Fun(var, Box::new(body))
  }

  pub fn app(fun: Self, arg: Self) -> Self {
    Self::App(Box::new(fun), Box::new(arg))
  }

  pub fn ty_fun(kind: Kind, ir: Self) -> Self {
    Self::TyFun(kind, Box::new(ir))
  }

  pub fn ty_app(ty_fun: Self, ty: Type) -> Self {
    Self::TyApp(Box::new(ty_fun), ty)
  }

  pub fn local(var: Var, defn: Self, body: Self) -> Self {
    Self::Local(var, Box::new(defn), Box::new(body))
  }

  pub fn type_of(&self) -> Type {
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

        ret_ty.subst_ty(ty.clone())
      }
      IR::Local(v, defn, body) => {
        if v.ty != defn.type_of() {
          panic!("ICE: Type mismatch local variable has different type from it's definition.")
        }
        body.type_of()
      }
    }
  }
}

#[derive(Default)]
pub struct VarSupply {
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

  pub fn supply(&mut self) -> VarId {
    let ir_var = self.next;
    self.next += 1;
    VarId(ir_var)
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
  let bound_lower_ty = (0..lower.env.len()).fold(lower_ty, |ty, _| Type::ty_fun(Kind::Type, ty));
  (bound_lower_ty, lower)
}

struct LowerAst {
  supply: VarSupply,
  types: LowerTypes,
}

impl LowerAst {
  fn lower_ast(&mut self, ast: Ast<TypedVar>) -> IR {
    match ast {
      Ast::Var(_, TypedVar(var, ty)) => IR::Var(Var::new(
        self.supply.supply_for(var),
        self.types.lower_ty(ty),
      )),
      Ast::Int(_, i) => IR::Int(i),
      Ast::Fun(_, TypedVar(var, ty), body) => {
        let ir_ty = self.types.lower_ty(ty);
        let ir_var = self.supply.supply_for(var);
        let ir_body = self.lower_ast(*body);
        IR::fun(Var::new(ir_var, ir_ty), ir_body)
      }
      Ast::App(_, fun, arg) => {
        let ir_fun = self.lower_ast(*fun);
        let ir_arg = self.lower_ast(*arg);
        IR::app(ir_fun, ir_arg)
      }
      Ast::Hole(_, _) => panic!("ICE: Hole encountered during lowering"),
    }
  }
}

pub fn lower(ast: Ast<TypedVar>, scheme: ast::TypeScheme) -> (IR, Type) {
  let (ir_ty, types) = lower_ty_scheme(scheme);
  let mut lower_ast = LowerAst {
    supply: VarSupply::default(),
    types,
  };
  let ir = lower_ast.lower_ast(ast);
  let bound_ir = (0..lower_ast.types.env.len()).fold(ir, |ir, _| IR::ty_fun(Kind::Type, ir));
  (bound_ir, ir_ty)
}

#[cfg(test)]
mod tests {
  use self::pretty::pretty_string;

  use super::*;
  use types_base::builder::AstBuilder;
  use types_base::{self as ast, type_infer, Ast};

  fn lower_test(ast: Ast<ast::Var>) -> (IR, Type) {
    let out = type_infer(ast);
    let (ir, ty) = lower(out.ast, out.scheme);
    (ir, ty)
  }

  #[test]
  fn lower_int() {
    let b = AstBuilder::default();
    let ast = b.int(3);

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir_ty, ir.type_of());

    let expect_ir = expect_test::expect!["3"];
    expect_ir.assert_eq(pretty_string(ir, 80).as_str());

    let expect_ir_ty = expect_test::expect!["Int"];
    expect_ir_ty.assert_eq(pretty_string(ir_ty, 80).as_str());
  }

  #[test]
  fn lower_id_fun() {
    let b = AstBuilder::default();
    let x = ast::Var(0);
    let ast = b.fun(x, b.var(x));

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir_ty, ir.type_of());

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          (fun [V0]
            V0))"#]];
    expect_ir.assert_eq(pretty_string(ir, 80).as_str());

    let expect_ir_ty = expect_test::expect![[r#"
        ty_fun [Type] .
          T0 -> T0"#]];
    expect_ir_ty.assert_eq(pretty_string(ir_ty, 80).as_str());
  }

  #[test]
  fn lower_k_combinator() {
    let b = AstBuilder::default();
    let x = ast::Var(0);
    let y = ast::Var(1);
    let ast = b.funs([x, y], b.var(x));

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir_ty, ir.type_of());

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (fun [V0, V1]
            V0))"#]];
    expect_ir.assert_eq(pretty_string(ir, 80).as_str());

    let expect_ir_ty = expect_test::expect![[r#"
        ty_fun [Type, Type] .
          T1 -> T0 -> T1"#]];
    expect_ir_ty.assert_eq(pretty_string(ir_ty, 80).as_str());
  }

  #[test]
  fn lower_s_combinator() {
    let b = AstBuilder::default();
    let x = ast::Var(0);
    let y = ast::Var(1);
    let z = ast::Var(2);
    let ast = b.funs(
      [x, y, z],
      b.app(b.app(b.var(x), b.var(z)), b.app(b.var(y), b.var(z))),
    );

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir_ty, ir.type_of());

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type Type Type]
          (fun [V0, V1, V2]
            (V0 V2 (V1 V2))))"#]];
    expect_ir.assert_eq(pretty_string(ir, 80).as_str());

    let expect_ir_ty = expect_test::expect![[r#"
        ty_fun [Type, Type, Type] .
          (T2 -> T0 -> T1) -> (T2 -> T0) -> T2 -> T1"#]];
    expect_ir_ty.assert_eq(pretty_string(ir_ty, 80).as_str());
  }
}
