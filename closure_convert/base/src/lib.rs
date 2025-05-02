use std::collections::BTreeMap;
use std::collections::BTreeSet;

use lowering_base::{self as ir};
use simplify_base::{IRExt as SimplifyExt, Param};
use std::collections::HashMap;

mod pretty;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct VarId(usize);

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct Var {
  pub id: VarId,
  pub ty: Type,
}

impl Ord for Var {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.id.cmp(&other.id)
  }
}
impl PartialOrd for Var {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct ItemId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IR {
  Var(Var),
  Int(i32),
  Closure(Type, ItemId, Vec<Var>),
  Apply(Box<Self>, Box<Self>),
  Local(Var, Box<Self>, Box<Self>),
  Access(Box<Self>, usize),
}

impl IR {
  pub fn apply(closure: Self, arg: Self) -> Self {
    Self::Apply(Box::new(closure), Box::new(arg))
  }

  pub fn local(var: Var, defn: Self, body: Self) -> Self {
    Self::Local(var, Box::new(defn), Box::new(body))
  }

  fn free_vars_aux(&self, free: &mut BTreeSet<Var>) {
    match self {
      IR::Var(var) => {
        free.insert(var.clone());
      }
      IR::Int(_) => {}
      IR::Closure(_, _, vars) => {
        for var in vars {
          free.insert(var.clone());
        }
      }
      IR::Apply(fun, arg) => {
        fun.free_vars_aux(free);
        arg.free_vars_aux(free);
      }
      IR::Local(var, defn, body) => {
        body.free_vars_aux(free);
        defn.free_vars_aux(free);
        free.remove(var);
      }
      IR::Access(ir, _) => ir.free_vars_aux(free),
    }
  }

  fn free_vars(&self) -> BTreeSet<Var> {
    let mut free = BTreeSet::default();
    self.free_vars_aux(&mut free);
    free
  }

  fn access(body: Self, field: usize) -> IR {
    IR::Access(Box::new(body), field)
  }

  fn rename(&mut self, subst: &HashMap<Var, Var>) {
    match self {
      IR::Var(var) => {
        if let Some(new_var) = subst.get(var) {
          *var = new_var.clone();
        }
      }
      IR::Int(_) => {}
      IR::Closure(_, _, vars) => {
        for var in vars.iter_mut() {
          if let Some(new_var) = subst.get(var) {
            *var = new_var.clone();
          }
        }
      }
      IR::Apply(fun, arg) => {
        fun.rename(subst);
        arg.rename(subst);
      }
      IR::Local(_, defn, body) => {
        defn.rename(subst);
        body.rename(subst);
      }
      IR::Access(body, _) => body.rename(subst),
    }
  }

  pub fn type_of(&self) -> Type {
    match self {
      IR::Var(var) => var.ty.clone(),
      IR::Int(_) => Type::I32,
      IR::Closure(ty, _, _) => ty.clone(),
      IR::Apply(closure, arg) => {
        let Type::Closure(arg_ty, ret_ty) = closure.type_of() else {
          panic!("ICE: Apply was applied to non closure type");
        };
        if *arg_ty != arg.type_of() {
          panic!("ICE: Closure was applied to argument of wrong type");
        }
        *ret_ty
      }
      IR::Local(_, _, body) => body.type_of(),
      IR::Access(strukt, field) => {
        let Type::ClosureEnv(_, env) = strukt.type_of() else {
          panic!("ICE: Access was applied to non closure env node");
        };
        env[*field].clone()
      }
    }
  }
}

pub struct Item {
  pub params: Vec<Var>,
  pub ret_ty: Type,
  pub body: IR,
}

#[derive(Default)]
pub struct VarSupply {
  next: usize,
  cache: HashMap<ir::VarId, VarId>,
}

impl VarSupply {
  fn supply_for(&mut self, var: ir::VarId) -> VarId {
    self
      .cache
      .entry(var)
      .or_insert_with(|| {
        let id = self.next;
        self.next += 1;
        VarId(id)
      })
      .to_owned()
  }

  pub fn supply(&mut self) -> VarId {
    let id = self.next;
    self.next += 1;
    VarId(id)
  }
}

#[derive(Default)]
struct ItemSupply {
  next: u32,
}

impl ItemSupply {
  fn supply(&mut self) -> ItemId {
    let item_id = self.next;
    self.next += 1;
    ItemId(item_id)
  }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Type {
  I32,
  Closure(Box<Type>, Box<Type>),
  ClosureEnv(Box<Type>, Vec<Type>),
}

impl Type {
  pub fn closure(arg: Self, ret: Self) -> Self {
    Self::Closure(Box::new(arg), Box::new(ret))
  }

  pub fn closure_env(closure: Self, env: Vec<Self>) -> Self {
    Self::ClosureEnv(Box::new(closure), env)
  }
}

fn lower_ty(ty: &ir::Type) -> Type {
  match ty {
    ir::Type::Int => Type::I32,
    ir::Type::Fun(arg, ret) => Type::closure(lower_ty(arg), lower_ty(ret)),
    ir::Type::Var(_) | ir::Type::TyFun(_, _) => panic!("ICE: Type function or variable appeared in closure conversion. This should've been handled by monomorphization."),
  }
}

struct ClosureConvert {
  var_supply: VarSupply,
  item_supply: ItemSupply,
  items: BTreeMap<ItemId, Item>,
}

impl ClosureConvert {
  fn make_closure(
    &mut self,
    var: Var,
    body: lowering_base::IR,
    env: im::HashMap<ir::Var, Var>,
  ) -> IR {
    let ret = lower_ty(&body.type_of());
    let mut body = self.convert(body.clone(), env);
    let mut free_vars = body.free_vars();
    free_vars.remove(&var);

    let vars: Vec<Var> = free_vars.iter().cloned().collect();
    let closure_ty = Type::closure(var.ty.clone(), ret.clone());
    let env_var = Var {
      id: self.var_supply.supply(),
      ty: Type::closure_env(
        closure_ty.clone(),
        vars.iter().map(|var| var.ty.clone()).collect(),
      ),
    };
    let subst = free_vars
      .into_iter()
      .enumerate()
      .map(|(i, var)| {
        let id = self.var_supply.supply();
        let new_var = Var {
          id,
          ty: var.ty.clone(),
        };
        body = IR::local(
          new_var.clone(),
          IR::access(IR::Var(env_var.clone()), i + 1),
          body.clone(),
        );
        (var, new_var)
      })
      .collect::<HashMap<_, _>>();

    let params = vec![env_var, var];
    body.rename(&subst);

    let item = self.item_supply.supply();
    self.items.insert(
      item,
      Item {
        params,
        ret_ty: ret,
        body,
      },
    );
    IR::Closure(closure_ty, item, vars)
  }

  fn convert(&mut self, ir: lowering_base::IR, env: im::HashMap<ir::Var, Var>) -> IR {
    match ir {
      lowering_base::IR::Var(var) => IR::Var(env[&var].clone()),
      lowering_base::IR::Int(i) => IR::Int(i.try_into().unwrap()),
      lowering_base::IR::Fun(fun_var, body) => {
        let var = Var {
          id: self.var_supply.supply_for(fun_var.id),
          ty: lower_ty(&fun_var.ty),
        };
        self.make_closure(var.clone(), *body, env.update(fun_var, var))
      }
      lowering_base::IR::App(fun, arg) => {
        let closure = self.convert(*fun, env.clone());
        let arg = self.convert(*arg, env);
        IR::apply(closure, arg)
      }
      lowering_base::IR::Local(var, defn, body) => {
        let defn = self.convert(*defn, env.clone());
        let v = Var {
          id: self.var_supply.supply_for(var.id),
          ty: lower_ty(&var.ty),
        };
        let body = self.convert(*body, env.update(var, v.clone()));
        IR::local(v, defn, body)
      }
      lowering_base::IR::TyFun(_, _) | lowering_base::IR::TyApp(_, _) => {
        panic!("ICE: Generics appeared after monomorphizing")
      }
    }
  }
}

pub struct ClosureConvertOutput {
  pub item: Item,
  pub closure_items: BTreeMap<ItemId, Item>,
}

pub fn closure_convert(ir: lowering_base::IR) -> ClosureConvertOutput {
  let (params, ir) = ir.split_funs();
  let mut var_supply = VarSupply::default();
  let mut env = im::HashMap::default();
  let params = params
    .into_iter()
    .map(|param| match param {
      Param::Ty(_) => panic!("ICE: Type function encountered after monomorphizing"),
      Param::Val(var) => {
        let id = var_supply.supply_for(var.id);
        let anf_var = Var {
          id,
          ty: lower_ty(&var.ty),
        };
        env.insert(var, anf_var.clone());
        anf_var
      }
    })
    .collect();

  let mut conversion = ClosureConvert {
    var_supply,
    item_supply: Default::default(),
    items: Default::default(),
  };

  let ret_ty = lower_ty(&ir.type_of());
  let body = conversion.convert(ir, env);
  ClosureConvertOutput {
    item: Item {
      params,
      ret_ty,
      body,
    },
    closure_items: conversion.items,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use expect_test::expect;
  use lowering_base::pretty::pretty_string;
  use lowering_base::{self as ir, lower, Type};
  use monomorph_base::monomorph;
  use simplify_base::simplify;
  use types_base::{self as ast, type_infer, Ast, builder::{make_vars, AstBuilder}};

  fn trivial_monomorph(ir: ir::IR) -> ir::IR {
    let mut types = vec![];
    let mut fun = &ir;
    // Assume all types are Int.
    // This can't be wrong for base because we don't yet support any interesting types.
    // Any function getting passed around will use a function type not a
    while let ir::IR::TyFun(_, body) = fun {
      types.push(Type::Int);
      fun = body;
    }
    monomorph(ir, types)
  }

  fn test_lamba_lift(ast: Ast<ast::Var>) -> ClosureConvertOutput {
    let (ast, scheme) = type_infer(ast).expect("Typechecking to succeed");
    let (ir, _) = lower(ast, scheme);
    closure_convert(trivial_monomorph(simplify(ir)))
  }

  #[test]
  fn closure_convert_test() {
    let b = AstBuilder::default();
    let [add, x, y, p, q, g, h, f] = make_vars();
    let ast = b.funs(
      [add, h],
      b.locals(
        [
          (f, b.funs([q, x], b.apps(b.var(add), [b.var(q), b.var(x)]))),
          (g, b.funs([p, y], b.apps(b.var(add), [b.var(p), b.var(y)]))),
        ],
        b.app(
          b.app(b.var(h), b.app(b.var(f), b.int(3))),
          b.app(b.var(g), b.int(5)),
        ),
      ),
    );

    let output = test_lamba_lift(ast);

    let expect = expect![[r#"
        func(V0:[i32 -> [i32 -> i32]], V1:[[i32 -> i32] -> [[i32 -> i32] -> i32]]) {
          (apply (apply V1 (closure item0 [V0])) (closure item1 [V0]))
        }"#]];
    expect.assert_eq(&pretty_string(output.item, 80));

    let closure_expects = vec![
      expect![[r#"
          func(V3:{ code: [i32 -> i32]
                  , env: {[i32 -> [i32 -> i32]]}
                  }, V2:i32) {
            (let (V4 V3[1]) (apply (apply V4 3) V2))
          }"#]],
      expect![[r#"
          func(V6:{ code: [i32 -> i32]
                  , env: {[i32 -> [i32 -> i32]]}
                  }, V5:i32) {
            (let (V7 V6[1]) (apply (apply V7 5) V5))
          }"#]],
    ];
    for ((_, defn), expect) in output.closure_items.into_iter().zip(closure_expects) {
      expect.assert_eq(&pretty_string(defn, 80));
    }
  }
}
