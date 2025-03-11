use std::collections::BTreeMap;
use std::collections::BTreeSet;

use lowering_base::{Type, Var, VarSupply, IR};
use simplify_base::{IRExt as SimplifyExt, Param};
use std::collections::HashMap;

mod pretty;

trait IRExt: Sized {
  fn is_trivial_app(&self) -> bool;

  fn anf(self, var_supply: &mut VarSupply) -> Self;

  fn free_vars(&self, function_names: &HashMap<Var, BTreeSet<Var>>) -> BTreeSet<Var>;

  fn rename(&mut self, subst: &HashMap<Var, Var>);

  fn collect_spine(self) -> (Self, Vec<Self>);
}

impl IRExt for IR {
  fn is_trivial_app(&self) -> bool {
    self.is_trivial()
      || match self {
        IR::App(fun, arg) => fun.is_trivial_app() && arg.is_trivial(),
        IR::TyApp(ty_fun, _) => ty_fun.is_trivial_app(),
        _ => false,
      }
  }

  fn anf(self, var_supply: &mut VarSupply) -> Self {
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
  }

  fn free_vars(&self, function_names: &HashMap<Var, BTreeSet<Var>>) -> BTreeSet<Var> {
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
  }

  fn rename(&mut self, subst: &HashMap<Var, Var>) {
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
  }

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
enum Atom {
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
enum Anf {
  Atom(Atom),
  Closure(DefinitionId, Vec<Var>),
  Call(Atom, Vec<Atom>),
  Blocks(Vec<Atom>),
  Access(Var, usize),
}

impl Anf {
  fn free_vars(&self) -> BTreeSet<Var> {
    fn aux(anf: &Anf, free: &mut BTreeSet<Var>) {
      match anf {
        Anf::Atom(atom) => atom.free_vars(free),
        Anf::Closure(_, vars) => {
          free.extend(vars.iter().cloned());
        }
        Anf::Call(head, spine) => {
          head.free_vars(free);
          for atom in spine.iter() {
            atom.free_vars(free);
          }
        }
        Anf::Blocks(elems) => {
          for atom in elems {
            atom.free_vars(free);
          }
        }
        Anf::Access(var, _) => {
          free.insert(var.clone());
        }
      }
    }
    let mut free = BTreeSet::default();
    aux(self, &mut free);
    free
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
      Anf::Call(head, spine) => {
        rename_atom(head, subst);
        for atom in spine {
          rename_atom(atom, subst);
        }
      }
      /*Anf::Locals(binds, body) => {
        for (_, defn) in binds {
          defn.rename(subst);
        }
        body.rename(subst);
      }*/
      Anf::Blocks(elems) => {
        for atom in elems {
          rename_atom(atom, subst);
        }
      }
      Anf::Access(var, _) => {
        if let Some(new_var) = subst.get(var) {
          *var = new_var.clone();
        }
      }
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Locals {
  binds: Vec<(Var, Anf)>,
  body: Anf,
}
impl Locals {
  fn new(binds: Vec<(Var, Anf)>, body: Anf) -> Self {
    Self { binds, body }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Definition {
  params: Vec<Var>,
  body: Locals,
}

trait IRTyExt {
  fn function_ty(self) -> (Vec<Type>, Type);
}
impl IRTyExt for Type {
  fn function_ty(self) -> (Vec<Type>, Type) {
    let mut params = vec![];
    let mut ty = self;
    while let Type::Fun(param, ret) = ty {
      params.push(*param);
      ty = *ret;
    }
    (params, ty)
  }
}

/*fn add_parameters(
  var_supply: &mut VarSupply,
  mut defn_vars: HashMap<Var, BTreeSet<Var>>,
  ir: IR,
) -> IR {
  match ir {
    IR::Var(var) => {
      let Some(extra_vars) = defn_vars.get(&var) else {
        // Our variable either doesn't bind a function, or binds a function with no free vars.
        // Carry on regardless.
        return IR::Var(var);
      };
      extra_vars
        .iter()
        .rfold(IR::Var(var), |fun, var| IR::app(fun, IR::Var(var.clone())))
    }
    IR::Int(i) => IR::Int(i),
    IR::Fun(var, body) => IR::fun(var, add_parameters(var_supply, defn_vars, *body)),
    IR::App(fun, arg) => IR::app(
      add_parameters(var_supply, defn_vars.clone(), *fun),
      add_parameters(var_supply, defn_vars, *arg),
    ),
    IR::TyFun(kind, body) => IR::ty_fun(kind, add_parameters(var_supply, defn_vars, *body)),
    IR::TyApp(ty_fun, ty_app) => IR::ty_app(add_parameters(var_supply, defn_vars, *ty_fun), ty_app),
    IR::Local(var, defn, body) => {
      let mut defn = add_parameters(var_supply, defn_vars.clone(), *defn);
      if matches!(defn, IR::Fun(_, _) | IR::TyFun(_, _)) {
        // We're binding a function we need to add it's free variables as parameters.
        let mut subst = HashMap::default();
        let free_vars = defn.free_vars(&defn_vars);
        // Include free vars for defn when adding parameters to body
        defn_vars.insert(var.clone(), free_vars.clone());
        let mut wrapped_fun = free_vars.into_iter().rfold(defn, |body, var| {
          let id = var_supply.supply();
          let new_var = Var {
            id,
            ty: var.ty.clone(),
          };
          subst.insert(var, new_var.clone());
          IR::fun(new_var, body)
        });
        wrapped_fun.rename(&subst);
        defn = wrapped_fun;
      }
      IR::local(var, defn, add_parameters(var_supply, defn_vars, *body))
    }
  }
}*/

fn eta_expand(var_supply: &mut VarSupply, ir: IR) -> IR {
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
}

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

struct ClosureConvert<'a> {
  var_supply: &'a mut VarSupply,
  defn_supply: &'a mut DefnSupply,
  defns: BTreeMap<DefinitionId, Definition>,
}

impl ClosureConvert<'_> {
  fn make_closure(&mut self, ir: IR) -> Anf {
    let (params, body) = ir.split_funs();
    let mut params = params
      .into_iter()
      .map(|param| match param {
        Param::Ty(_) => panic!("ICE: type function encountered after monomorphizing"),
        Param::Val(var) => var,
      })
      .collect::<Vec<_>>();
    let mut binds = vec![];
    let mut body = self.convert(body.clone(), &mut binds);
    let mut free_vars = body.free_vars();
    for var in &params {
        free_vars.remove(var);
    }

    let id = self.var_supply.supply();
    // TODO: Clean this up.
    // Figure out if we want to include types at this stage or not.
    // I lean towards yes we need some form of typing for targeting wasm.
    let env_var = Var { id, ty: Type::Int };
    let mut vars = vec![];
    let subst = free_vars
      .into_iter()
      .enumerate()
      .map(|(i, var)| {
        vars.push(var.clone());
        let id = self.var_supply.supply();
        let new_var = Var {
          id,
          ty: var.ty.clone(),
        };
        binds.insert(0, (new_var.clone(), Anf::Access(env_var.clone(), i)));
        (var, new_var)
      })
      .collect::<HashMap<_, _>>();

    params.insert(0, env_var);
    body.rename(&subst);

    let item = self.defn_supply.supply();
    self.defns.insert(
      item,
      Definition {
        params,
        body: Locals::new(binds, body),
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

  fn convert(&mut self, ir: IR, binds: &mut Vec<(Var, Anf)>) -> Anf {
    match ir {
      IR::Var(var) => Anf::Atom(Atom::Var(var)),
      IR::Int(i) => Anf::Atom(Atom::Int(i)),
      ir @ IR::Fun(_, _) => self.make_closure(ir),
      ir @ IR::App(_, _) => {
        let (head, spine) = ir.collect_spine();
        let spine = spine
          .into_iter()
          .map(|ir| {
            let ty = ir.type_of();
            let anf = self.convert(ir, binds);
            self.make_atom(ty, anf, binds)
          })
          .collect::<Vec<_>>();
        let ty = head.type_of();
        let anf = self.convert(head, binds);
        let head = self.make_atom(ty, anf, binds);
        Anf::Call(head, spine)
      }
      IR::Local(var, defn, body) => {
        let defn = self.convert(*defn, binds);
        binds.push((var, defn));
        self.convert(*body, binds)
      }
      IR::TyFun(_, _) | IR::TyApp(_, _) => panic!("ICE: type function or application "),
    }
  }
}

pub struct ClosureConvertOutput {
  defn: Definition,
  closure_defns: BTreeMap<DefinitionId, Definition>,
}

pub fn closure_convert(var_supply: &mut VarSupply, ir: IR) -> ClosureConvertOutput {
  let (params, ir) = ir.split_funs();
  let eta_ir = eta_expand(var_supply, ir);
  let mut defn_supply = DefnSupply::default();
  let mut conversion = ClosureConvert {
    var_supply,
    defn_supply: &mut defn_supply,
    defns: Default::default(),
  };

  let mut binds = vec![];
  let body = conversion.convert(eta_ir, &mut binds);
  ClosureConvertOutput {
    defn: Definition {
      params: params
        .into_iter()
        .map(|param| match param {
          Param::Ty(_) => panic!("ICE: type function encountered after monomorphizing"),
          Param::Val(var) => var,
        })
        .collect(),
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
    let (ir, _, mut supply) = lower(ast, scheme);
    closure_convert(&mut supply, trivial_monomorph(simplify(ir)))
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
        defn(V0, V1) {
          V10 = (closure item0 [V0]);
          V13 = (closure item1 [V0]);
          (V1 V10 V13)
        }"#]];
    expect.assert_eq(&pretty_string(output.defn, 80));

    let closure_expects = vec![
      expect![[r#"
          defn(V8, V7) {
            V9 = V8[0];
            (V9 3 V7)
          }"#]],
      expect![[r#"
          defn(V11, V5) {
            V12 = V11[0];
            (V12 5 V5)
          }"#]],
    ];
    for ((_, defn), expect) in output.closure_defns.into_iter().zip(closure_expects) {
      expect.assert_eq(&pretty_string(defn, 80));
    }
  }
}
