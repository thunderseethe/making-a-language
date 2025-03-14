use std::any::Any;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use lowering_base::pretty::pretty_string;
use lowering_base::{self as ir, IR};
use simplify_base::{IRExt as SimplifyExt, Param};
use std::collections::HashMap;

mod pretty;

trait IRExt: Sized {
  //fn is_trivial_app(&self) -> bool;

  //fn anf(self, var_supply: &mut VarSupply) -> Self;

  //fn free_vars(&self, function_names: &HashMap<ir::Var, BTreeSet<ir::Var>>) -> BTreeSet<ir::Var>;

  //fn rename(&mut self, subst: &HashMap<Var, Var>);

  fn collect_spine(self) -> (Self, Vec<Self>);
}

impl IRExt for IR {
  /*fn is_trivial_app(&self) -> bool {
    self.is_trivial()
      || match self {
        IR::App(fun, arg) => fun.is_trivial_app() && arg.is_trivial(),
        IR::TyApp(ty_fun, _) => ty_fun.is_trivial_app(),
        _ => false,
      }
  }*/

  /*fn anf(self, var_supply: &mut VarSupply) -> Self {
    fn aux(locals: &mut Vec<(Var, IR)>, var_supply: &mut VarSupply, ir: IR) -> IR {
      let mut make_trivial_app = |ir: IR| {
        if ir.is_trivial_app() {
          return ir;
        }
        let defn = aux(locals, var_supply, ir);
        let id = var_supply.supply();
        let var = Var {
          id,
          ty: defn.type_of(),
        };
        locals.push((var.clone(), defn));
        IR::Var(var)
      };
      match ir {
        IR::Var(_) => ir,
        IR::Int(_) => ir,
        IR::Fun(var, ir) => IR::fun(var, ir.anf(var_supply)),
        IR::TyFun(kind, ir) => IR::ty_fun(kind, ir.anf(var_supply)),
        IR::App(fun, arg) => {
          let arg = make_trivial_app(*arg);
          let fun = make_trivial_app(*fun);
          IR::app(fun, arg)
        }
        IR::TyApp(ty_fun, ty) => {
          let ty_fun = make_trivial_app(*ty_fun);
          IR::ty_app(ty_fun, ty)
        }
        IR::Local(var, defn, body) => {
          let defn = aux(locals, var_supply, *defn);
          locals.push((var, defn));
          aux(locals, var_supply, *body)
        }
      }
    }
    let mut binds = vec![];
    let ir = aux(&mut binds, var_supply, self);
    binds
      .into_iter()
      .rfold(ir, |body, (var, defn)| IR::local(var, defn, body))
  }*/

  /*fn free_vars(&self, function_names: &HashMap<ir::Var, BTreeSet<ir::Var>>) -> BTreeSet<ir::Var> {
    match self {
      IR::Int(_) => BTreeSet::default(),
      IR::Var(var) => {
        if function_names.contains_key(var) {
          // Don't include functions in our free vars.
          // These are going to end up as top level definitions so won't be free after lambda
          // lifting.
          BTreeSet::default()
        } else {
          let mut free = BTreeSet::default();
          free.insert(var.clone());
          free
        }
      }
      IR::Fun(var, body) => {
        let mut free = body.free_vars(function_names);
        free.remove(var);
        free
      }
      IR::App(fun, arg) => {
        let mut fun_free = fun.free_vars(function_names);
        let arg_free = arg.free_vars(function_names);
        fun_free.extend(arg_free);
        fun_free
      }
      IR::TyFun(_, body) => body.free_vars(function_names),
      IR::TyApp(ty_fun, _) => ty_fun.free_vars(function_names),
      IR::Local(var, defn, body) => {
        let mut defn_free = defn.free_vars(function_names);
        let body_free = body.free_vars(function_names);
        defn_free.extend(body_free);
        defn_free.remove(var);
        defn_free
      }
    }
  }*/

  /*fn rename(&mut self, subst: &HashMap<Var, Var>) {
    match self {
      IR::Var(var) => {
        if let Some(new_var) = subst.get(var) {
          *var = new_var.clone();
        }
      }
      IR::Int(_) => {}
      IR::Fun(_, body) => body.rename(subst),
      IR::App(fun, arg) => {
        fun.rename(subst);
        arg.rename(subst);
      }
      IR::TyFun(_, body) => body.rename(subst),
      IR::TyApp(body, _) => body.rename(subst),
      IR::Local(_, defn, body) => {
        defn.rename(subst);
        body.rename(subst);
      }
    }
  }*/

  fn collect_spine(self) -> (Self, Vec<Self>) {
    let mut spine = vec![];
    let mut head = self;
    while let IR::App(fun, arg) = head {
      spine.push(*arg);
      head = *fun;
    }
    spine.reverse();
    (head, spine)
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct DefinitionId(u32);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Atom {
  Var(Var),
  Int(isize),
}

impl Atom {
  fn free_vars(&self, free: &mut BTreeSet<Var>) {
    match self {
      Atom::Var(var) => {
        free.insert(var.clone());
      }
      Atom::Int(_) => {}
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Anf {
  Atom(Atom),
  Closure(DefinitionId, Vec<Var>),
  Apply(Var, Atom),
  Access(Var, usize),
}

impl Anf {
  fn free_vars(&self, free: &mut BTreeSet<Var>) {
    match self {
      Anf::Atom(atom) => atom.free_vars(free),
      Anf::Closure(_, vars) => {
        free.extend(vars.iter().cloned());
      }
      Anf::Apply(head, arg) => {
        Atom::Var(head.clone()).free_vars(free);
        arg.free_vars(free);
      }
      Anf::Access(var, _) => {
        free.insert(var.clone());
      }
    }
  }

  fn rename(&mut self, subst: &HashMap<Var, Var>) {
    fn rename_atom(atom: &mut Atom, subst: &HashMap<Var, Var>) {
      let Atom::Var(var) = atom else { return };
      if let Some(new_var) = subst.get(var) {
        *var = new_var.clone();
      }
    }
    match self {
      Anf::Atom(atom) => rename_atom(atom, subst),
      Anf::Closure(_, vars) => {
        for var in vars {
          if let Some(new_var) = subst.get(var) {
            *var = new_var.clone();
          }
        }
      }
      Anf::Apply(head, arg) => {
        if let Some(new_head) = subst.get(head) {
          *head = new_head.clone();
        }
        rename_atom(arg, subst);
      }
      Anf::Access(var, _) => {
        if let Some(new_var) = subst.get(var) {
          *var = new_var.clone();
        }
      }
    }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct VarId(usize);

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Type {
  I32,
  Closure(Box<Type>, Box<Type>),
  Struct(Vec<Type>),
}

impl Type {
  fn closure(arg: Self, ret: Self) -> Self {
    Self::Closure(Box::new(arg), Box::new(ret))
  }
}

fn lower_ty(ty: &ir::Type) -> Type {
  match ty {
    ir::Type::Int => Type::I32,
    ir::Type::Fun(arg, ret) => Type::closure(lower_ty(arg), lower_ty(ret)),
    ir::Type::Var(_) | ir::Type::TyFun(_, _) => panic!("ICE: Type function or variable appeared in closure conversion. This should've been handled by monomorphization."),
  }
}

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Locals {
  pub binds: Vec<(Var, Anf)>,
  pub body: Anf,
}
impl Locals {
  fn new(binds: Vec<(Var, Anf)>, body: Anf) -> Self {
    Self { binds, body }
  }

  fn rename(&mut self, subst: &HashMap<Var, Var>) {
    for (_, defn) in &mut self.binds {
      defn.rename(subst);
    }
    self.body.rename(subst);
  }


  fn free_vars(&self) -> BTreeSet<Var> {
    let mut free = BTreeSet::default();
    self.body.free_vars(&mut free);
    for (var, defn) in self.binds.iter().rev() {
        defn.free_vars(&mut free);
        free.remove(var);
    }
    free
  }

  fn prepend_bind(&mut self, var: Var, defn: Anf) {
    self.binds.insert(0, (var, defn));
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition {
  pub params: Vec<Var>,
  pub body: Locals,
}

/*trait IRTyExt {
  fn function_ty(self) -> (Vec<Type>, Type);
}
impl IRTyExt for ir::Type {
  fn function_ty(self) -> (Vec<Type>, Type) {
    let mut params = vec![];
    let mut ty = self;
    while let ir::Type::Fun(param, ret) = ty {
      params.push(*param);
      ty = *ret;
    }
    (params, ty)
  }
}*/

/*fn eta_expand(var_supply: &mut ir::VarSupply, ir: IR) -> IR {
  match ir {
    ir @ IR::App(_, _) => {
      let (head, spine) = ir.collect_spine();
      let (params, _) = head.type_of().function_ty();
      let arg_count = spine.len();
      let mut body = spine.into_iter().fold(head, |fun, arg| {
        IR::app(fun, eta_expand(var_supply, arg.clone()))
      });
      if arg_count < params.len() {
        let mut vars = vec![];
        for ty in params.into_iter().skip(arg_count) {
          let id = var_supply.supply();
          let var = Var { id, ty };
          body = IR::app(body, IR::Var(var.clone()));
          vars.push(var);
        }
        body = vars.into_iter().rfold(body, |body, var| IR::fun(var, body));
      }
      body
    }
    IR::Fun(var, body) => IR::fun(var, eta_expand(var_supply, *body)),
    IR::TyFun(kind, body) => IR::ty_fun(kind, eta_expand(var_supply, *body)),
    IR::TyApp(ty_fun, ty) => IR::ty_app(*ty_fun, ty),
    IR::Local(var, defn, body) => IR::local(
      var,
      eta_expand(var_supply, *defn),
      eta_expand(var_supply, *body),
    ),
    IR::Var(v) => IR::Var(v),
    IR::Int(i) => IR::Int(i),
  }
}*/

#[derive(Default)]
struct DefnSupply {
  next: u32,
}

impl DefnSupply {
  fn supply(&mut self) -> DefinitionId {
    let defn_id = self.next;
    self.next += 1;
    DefinitionId(defn_id)
  }
}

struct ClosureConvert {
  var_supply: VarSupply,
  defn_supply: DefnSupply,
  defns: BTreeMap<DefinitionId, Definition>,
}

impl ClosureConvert {
  fn make_closure(&mut self, var: Var, body: IR, env: im::HashMap<ir::Var, Var>) -> Anf {
    //let (params, body) = ir.split_funs();
    let mut binds = vec![];
    let body = self.convert(body.clone(), &mut binds, env);
    //let mut free_vars = body.free_vars();
    let mut locals = Locals::new(binds, body);
    let mut free_vars = locals.free_vars();
    free_vars.remove(&var);
    println!("{:?}", free_vars.iter().map(|v| {
      let mut str = pretty_string(v.clone(), 80).clone();
      str.push(' ');
      str.push_str(&pretty_string(v.ty.clone(), 80));
      str
    }).collect::<Vec<_>>());

    // TODO: Clean this up.
    // Figure out if we want to include types at this stage or not.
    // I lean towards yes we need some form of typing for targeting wasm.
    let vars: Vec<Var> = free_vars.iter().cloned().collect();
    let env_var = Var {
      id: self.var_supply.supply(),
      ty: Type::Struct(vars.iter().map(|var| var.ty.clone()).collect()),
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
        locals.prepend_bind(new_var.clone(), Anf::Access(env_var.clone(), i));
        (var, new_var)
      })
      .collect::<HashMap<_, _>>();

    let params = vec![env_var, var];
    locals.rename(&subst);

    let item = self.defn_supply.supply();
    self.defns.insert(
      item,
      Definition {
        params,
        body: locals
      },
    );
    Anf::Closure(item, vars)
  }

  fn make_atom(&mut self, ty: Type, anf: Anf, binds: &mut Vec<(Var, Anf)>) -> Atom {
    if let Anf::Atom(atom) = anf {
      atom
    } else {
      let id = self.var_supply.supply();
      let var = Var { id, ty };
      binds.push((var.clone(), anf));
      Atom::Var(var)
    }
  }

  fn convert(
    &mut self,
    ir: IR,
    binds: &mut Vec<(Var, Anf)>,
    env: im::HashMap<ir::Var, Var>,
  ) -> Anf {
    match ir {
      IR::Var(var) => Anf::Atom(Atom::Var(env[&var].clone())),
      IR::Int(i) => Anf::Atom(Atom::Int(i)),
      IR::Fun(var, body) => {
        let anf_var = Var {
          id: self.var_supply.supply_for(var.id),
          ty: lower_ty(&var.ty),
        };
        self.make_closure(anf_var.clone(), *body, env.update(var, anf_var))
      }
      IR::App(fun, arg) => {
        //let (head, spine) = ir.collect_spine();
        /*let spine = spine
          .into_iter()
          .map(|ir| {
            let ty = ir.type_of();
            let anf = self.convert(ir, binds, env.clone());
            // TODO: Get type out of `anf`, so that we respect our type env.
            self.make_atom(lower_ty(&ty), anf, binds)
          })
          .collect::<Vec<_>>();*/
        let arg_ty = arg.type_of();
        let anf_arg = self.convert(*arg, binds, env.clone());
        let arg = self.make_atom(lower_ty(&arg_ty), anf_arg, binds);

        let fun_ty = fun.type_of();
        let anf_fun = self.convert(*fun.clone(), binds, env.clone());
        // TODO: Get type out of `anf`, so that we respect our type env.
        let Atom::Var(closure) = self.make_atom(lower_ty(&fun_ty), anf_fun, binds) else {
          panic!("ICE: Tried to call an int as a function");
        };
        Anf::Apply(closure, arg)
      }
      IR::Local(var, defn, body) => {
        let defn = self.convert(*defn, binds, env.clone());
        let anf_var = Var {
          id: self.var_supply.supply_for(var.id),
          ty: lower_ty(&var.ty),
        };
        binds.push((anf_var, defn));
        self.convert(*body, binds, env)
      }
      IR::TyFun(_, _) | IR::TyApp(_, _) => panic!("ICE: type function or application "),
    }
  }
}

pub struct ClosureConvertOutput {
  defn: Definition,
  closure_defns: BTreeMap<DefinitionId, Definition>,
}

pub fn closure_convert(ir: IR) -> ClosureConvertOutput {
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
    defn_supply: DefnSupply::default(),
    defns: Default::default(),
  };

  let mut binds = vec![];
  let body = conversion.convert(ir, &mut binds, env);
  ClosureConvertOutput {
    defn: Definition {
      params,
      body: Locals::new(binds, body),
    },
    closure_defns: conversion.defns,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use expect_test::expect;
  use lowering_base::pretty::pretty_string;
  use lowering_base::{lower, Type};
  use monomorph_base::monomorph;
  use simplify_base::simplify;
  use types_base::{self as ast, type_infer, Ast};

  fn trivial_monomorph(ir: IR) -> IR {
    let mut types = vec![];
    let mut fun = &ir;
    // Assume all types are Int.
    // This can't be wrong for base because we don't yet support any interesting types.
    // Any function getting passed around will use a function type not a
    while let IR::TyFun(_, body) = fun {
      types.push(Type::Int);
      fun = body;
    }
    monomorph(ir, types)
  }

  fn test_lamba_lift(ast: Ast<ast::Var>) -> ClosureConvertOutput {
    let (ast, scheme) = type_infer(ast).expect("Typechecking to succeed");
    let (ir, _, _) = lower(ast, scheme);
    closure_convert(trivial_monomorph(simplify(ir)))
  }

  fn locals(
    binds: impl IntoIterator<Item = (ast::Var, Ast<ast::Var>)>,
    body: Ast<ast::Var>,
  ) -> Ast<ast::Var> {
    binds
      .into_iter()
      .collect::<Vec<_>>()
      .into_iter()
      .rfold(body, |body, (var, defn)| {
        Ast::app(Ast::fun(var, body), defn)
      })
  }

  #[test]
  fn closure_convert_test() {
    let add = ast::Var(0);
    let x = ast::Var(1);
    let y = ast::Var(2);
    let p = ast::Var(3);
    let q = ast::Var(4);
    let g = ast::Var(5);
    let h = ast::Var(6);
    let f = ast::Var(7);
    let ast = Ast::fun(
      add,
      Ast::fun(
        h,
        locals(
          [
            (
              f,
              Ast::fun(
                q,
                Ast::fun(
                  x,
                  Ast::app(Ast::app(Ast::Var(add), Ast::Var(q)), Ast::Var(x)),
                ),
              ),
            ),
            (
              g,
              Ast::fun(
                p,
                Ast::fun(
                  y,
                  Ast::app(Ast::app(Ast::Var(add), Ast::Var(p)), Ast::Var(y)),
                ),
              ),
            ),
          ],
          Ast::app(
            Ast::app(Ast::Var(h), Ast::app(Ast::Var(f), Ast::Int(3))),
            Ast::app(Ast::Var(g), Ast::Int(5)),
          ),
        ),
      ),
    );

    let output = test_lamba_lift(ast);

    let expect = expect![[r#"
        defn(V0:〚i32 -> 〚i32 -> i32〛〛, V1:〚〚i32 -> i32〛 ->
          〚〚i32 -> i32〛 -> i32〛〛) {
          V6: 〚i32 -> i32〛 = (closure item0 [V0]);
          V11: 〚i32 -> i32〛 = (closure item1 [V0]);
          V12: 〚〚i32 -> i32〛 -> i32〛 = (apply V1 V11);
          (apply V12 V6)
        }"#]];
    expect.assert_eq(&pretty_string(output.defn, 80));

    let closure_expects = vec![
      expect![[r#"
          defn(V4:{〚i32 -> 〚i32 -> i32〛〛}, V2:i32) {
            V5: 〚i32 -> 〚i32 -> i32〛〛 = V4[0];
            V3: 〚i32 -> i32〛 = (apply V5 5);
            (apply V3 V2)
          }"#]],
      expect![[r#"
          defn(V9:{〚i32 -> 〚i32 -> i32〛〛}, V7:i32) {
            V10: 〚i32 -> 〚i32 -> i32〛〛 = V9[0];
            V8: 〚i32 -> i32〛 = (apply V10 3);
            (apply V8 V7)
          }"#]],
    ];
    for ((_, defn), expect) in output.closure_defns.into_iter().zip(closure_expects) {
      expect.assert_eq(&pretty_string(defn, 80));
    }
  }
}
