use std::collections::HashMap;

use lowering_base::pretty::pretty_string;
use lowering_base::{Kind, Type, Var, VarId, IR};

enum Param {
  Ty(Kind),
  Val(Var),
}

trait IRExt {
  fn is_trivial(&self) -> bool;

  fn is_value(&self) -> bool;

  fn within_toplevel_funs(self, body: impl FnOnce(&Vec<Param>, IR) -> IR) -> IR;

  fn split_funs(&self) -> (Vec<Param>, &IR);

  fn size(&self) -> usize;
}
impl IRExt for IR {
  fn is_trivial(&self) -> bool {
    matches!(self, IR::Var(_) | IR::Int(_))
  }

  fn is_value(&self) -> bool {
    match self {
      IR::Var(_) | IR::Int(_) | IR::Fun(_, _) => true,
      IR::TyFun(_, ir) => ir.is_value(),
      IR::TyApp(ir, _) => ir.is_value(),
      IR::Local(_, defn, body) => defn.is_value() && body.is_value(),
      IR::App(_, _) => false,
    }
  }

  fn within_toplevel_funs(self, fun: impl FnOnce(&Vec<Param>, IR) -> IR) -> IR {
    let mut params = vec![];
    let mut cursor = self;
    let body = loop {
      match cursor {
        IR::TyFun(kind, ir) => {
          params.push(Param::Ty(kind));
          cursor = *ir;
        }
        IR::Fun(var, ir) => {
          params.push(Param::Val(var));
          cursor = *ir;
        }
        ir => break ir,
      }
    };
    let body = fun(&params, body);
    params.into_iter().rfold(body, |body, param| match param {
      Param::Ty(kind) => IR::ty_fun(kind, body),
      Param::Val(var) => IR::fun(var, body),
    })
  }
  fn split_funs(&self) -> (Vec<Param>, &IR) {
    fn split_funs<'a>(ir: &'a IR, params: &mut Vec<Param>) -> &'a IR {
      match ir {
        IR::TyFun(kind, ir) => {
          params.push(Param::Ty(*kind));
          split_funs(ir, params)
        }
        IR::Fun(var, ir) => {
          params.push(Param::Val(var.clone()));
          split_funs(ir, params)
        }
        ir => ir,
      }
    }
    let mut params = vec![];
    let body = split_funs(self, &mut params);
    (params, body)
  }

  fn size(&self) -> usize {
    fn size_app(ir: &IR, arg_count: usize) -> usize {
      match ir {
        IR::App(fun, _) => size_app(fun, arg_count + 1),
        IR::TyApp(ir, _) => size_app(ir, arg_count),
        IR::Var(_) => {
          if arg_count > 0 {
            1 + arg_count
          } else {
            0
          }
        }
        ir => ir.size() + arg_count,
      }
    }
    match self {
      IR::Var(_) | IR::Int(_) => 0,
      IR::Fun(_, body) => 1 + body.size(),
      IR::App(fun, _) => size_app(fun, 1),
      IR::TyFun(_, ir) => ir.size(),
      IR::TyApp(ir, _) => ir.size(),
      IR::Local(var, defn, body) => {
        defn.size() + body.size() + (if var.ty.is_stack_alloc() { 0 } else { 1 })
      }
    }
  }
}

trait TypeExt {
  fn is_stack_alloc(&self) -> bool;
}
impl TypeExt for Type {
  fn is_stack_alloc(&self) -> bool {
    // Our only stack allocated type is Int
    matches!(self, Type::Int)
  }
}

fn subst_ty(haystack: IR, payload: Type) -> IR {
  match haystack {
    IR::Var(var) => IR::Var(var.map_ty(|ty| ty.subst_ty(payload))),
    IR::Int(i) => IR::Int(i),
    IR::Fun(var, ir) => IR::fun(
      var.map_ty(|ty| ty.subst_ty(payload.clone())),
      subst_ty(*ir, payload),
    ),
    IR::App(fun, arg) => IR::app(subst_ty(*fun, payload.clone()), subst_ty(*arg, payload)),
    IR::TyFun(kind, ir) => IR::ty_fun(kind, subst_ty(*ir, payload)),
    IR::TyApp(ir, ty) => IR::ty_app(subst_ty(*ir, payload.clone()), ty.subst_ty(payload)),
    IR::Local(var, defn, body) => IR::local(
      var.map_ty(|ty| ty.subst_ty(payload.clone())),
      subst_ty(*defn, payload.clone()),
      subst_ty(*body, payload),
    ),
  }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Occurrence {
  Dead,
  Once,
  OnceInFun,
  Many,
}

#[derive(Default, Debug)]
struct Occurrences {
  vars: HashMap<VarId, Occurrence>,
}
impl Occurrences {
  fn with_var_once(var: VarId) -> Self {
    let mut vars = HashMap::default();
    vars.insert(var, Occurrence::Once);
    Self { vars }
  }

  fn in_fun(self) -> Self {
    Self {
      vars: self
        .vars
        .into_iter()
        .map(|(id, occ)| {
          (
            id,
            match occ {
              Occurrence::Once => Occurrence::OnceInFun,
              occ => occ,
            },
          )
        })
        .collect(),
    }
  }

  fn merge_internal(&mut self, other: Self, once_meet: Occurrence) {
    for (var, occ) in other.vars {
      self
        .vars
        .entry(var)
        .and_modify(|self_occ| {
          *self_occ = match (*self_occ, occ) {
            (Occurrence::Dead, occ) | (occ, Occurrence::Dead) => occ,
            (Occurrence::Many, _) | (_, Occurrence::Many) => Occurrence::Many,
            (Occurrence::Once, Occurrence::Once) => once_meet,
            (Occurrence::Once, _) | (Occurrence::OnceInFun, _) => Occurrence::Many,
          };
        })
        .or_insert(occ);
    }
  }

  fn merge_mut(&mut self, other: Self) {
    self.merge_internal(other, Occurrence::Many);
  }

  fn merge(mut self, other: Self) -> Self {
    self.merge_mut(other);
    self
  }

  fn lookup_var(&self, var: &Var) -> Occurrence {
    self.vars.get(&var.id).copied().unwrap_or(Occurrence::Dead)
  }
}

fn occurrence_analysis(ir: IR) -> (IR, Occurrences) {
  match ir {
    IR::Var(var) => {
      let occs = Occurrences::with_var_once(var.id);
      (IR::Var(var), occs)
    }
    IR::Int(i) => (IR::Int(i), Occurrences::default()),
    IR::Fun(var, ir) => {
      let (body, occs) = occurrence_analysis(*ir);
      (IR::fun(var, body), occs.in_fun())
    }
    IR::App(fun, arg) => {
      let (fun, fun_occs) = occurrence_analysis(*fun);
      let (arg, arg_occs) = occurrence_analysis(*arg);
      (IR::app(fun, arg), fun_occs.merge(arg_occs))
    }
    IR::TyFun(kind, ir) => {
      let (body, occs) = occurrence_analysis(*ir);
      (IR::ty_fun(kind, body), occs)
    }
    IR::TyApp(ir, ty_app) => {
      let (ty_fun, occs) = occurrence_analysis(*ir);
      (IR::ty_app(ty_fun, ty_app), occs)
    }
    IR::Local(var, defn, body) => {
      let (body, occs) = occurrence_analysis(*body);
      // Immediately strip away a dead binding.
      if let Occurrence::Dead = occs.lookup_var(&var) {
        (body, occs)
      } else {
        // Only add occurrences if our binding isn't dead.
        let (defn, defn_occs) = occurrence_analysis(*defn);
        (IR::local(var, defn, body), defn_occs.merge(occs))
      }
    }
  }
}

#[derive(Debug, Clone)]
enum SubstRng {
  Suspend(IR, Subst),
  Done(IR),
}
type Subst = HashMap<VarId, SubstRng>;

#[derive(Debug, Clone)]
enum Definition {
  Unknown,
  BoundTo(IR, Occurrence),
}
type InScope = HashMap<VarId, Definition>;

#[derive(Debug)]
struct Simplifier {
  // state to perform simplification
  occs: Occurrences,
  subst: Subst,
  in_scope: InScope,
  ctx: Context,

  // stats, used to determine if we simplified
  saturated_fun_count: usize,
  saturated_ty_fun_count: usize,
  locals_inlined: usize,

  // configurable flags for simplification
  inline_size_threshold: usize,
}

impl Default for Simplifier {
  fn default() -> Self {
    Self {
      inline_size_threshold: 60,
      occs: Default::default(),
      subst: Default::default(),
      in_scope: Default::default(),
      ctx: Default::default(),
      saturated_fun_count: Default::default(),
      saturated_ty_fun_count: Default::default(),
      locals_inlined: Default::default(),
    }
  }
}

#[derive(Debug)]
enum ContextEntry {
  AppContext(IR, Subst),
  TyAppContext(Type, Subst),
}

type Context = Vec<ContextEntry>;

impl Simplifier {
  fn new(in_scope: InScope, occs: Occurrences) -> Self {
    Self {
      in_scope,
      occs,
      ..Default::default()
    }
  }

  fn some_benefit(&self, ir: &IR) -> bool {
    let (params, _) = ir.split_funs();
    // If we have a non trivial argument in context, there's some benefit.
    if self.ctx.iter().take(params.len()).any(|entry| match entry {
      ContextEntry::AppContext(arg, _) => !arg.is_trivial(),
      _ => false,
    }) {
      return true;
    }

    // We have enough arguments to saturate our parameters.
    // We know this is a local function so there is benefit to inline
    if self.ctx.len() > params.len() {
      return true;
    }

    // If we saturate all args to our function and then apply more args to the body there is value
    // in inlining.
    matches!(
      self.ctx.get(params.len()),
      Some(ContextEntry::AppContext(_, _))
    )
  }

  fn in_snapshot<T>(&mut self, cont: impl FnOnce(&mut Self) -> T) -> T {
    let ctx = std::mem::take(&mut self.ctx);
    let in_scope = self.in_scope.clone();
    let result = cont(self);
    self.ctx = ctx;
    self.in_scope = in_scope;
    result
  }

  fn rebuild(&mut self, mut ir: IR) -> IR {
    while let Some(cont) = self.ctx.pop() {
      match cont {
        ContextEntry::AppContext(arg, env) => {
          self.subst = env;
          ir = if let IR::Fun(var, body) = ir {
            self.saturated_fun_count += 1;
            self.simplify(IR::local(var, arg, *body))
          } else {
            let arg = self.simplify(arg);
            IR::app(ir, arg)
          };
        }
        ContextEntry::TyAppContext(ty, env) => {
          self.subst = env;
          ir = if let IR::TyFun(_, body) = ir {
            self.saturated_ty_fun_count += 1;
            subst_ty(*body, ty)
          } else {
            IR::ty_app(ir, ty)
          };
        }
      }
    }
    ir
  }

  fn simplify(&mut self, ir: IR) -> IR {
    match ir {
      IR::App(fun, arg) => {
        self
          .ctx
          .push(ContextEntry::AppContext(*arg, self.subst.clone()));
        self.simplify(*fun)
      }
      IR::TyApp(ty_fun, ty_app) => {
        self
          .ctx
          .push(ContextEntry::TyAppContext(ty_app, self.subst.clone()));
        self.simplify(*ty_fun)
      }
      IR::TyFun(kind, body) => {
        let body = self.in_snapshot(|this| this.simplify(*body));
        self.rebuild(IR::ty_fun(kind, body))
      }
      IR::Fun(var, body) => {
        let body = self.in_snapshot(|this| {
          this.in_scope.insert(var.id, Definition::Unknown);
          this.simplify(*body)
        });
        self.rebuild(IR::fun(var, body))
      }
      IR::Local(var, defn, body) => {
        let occ = self.occs.lookup_var(&var);
        println!("{:?}", self.occs);
        if let Occurrence::Once = occ {
          self.locals_inlined += 1;
          let subst = self.subst.clone();
          self.subst.insert(var.id, SubstRng::Suspend(*defn, subst));
          self.simplify(*body)
        } else {
          let simple_defn = self.simplify(*defn);
          if simple_defn.is_trivial() {
            self.locals_inlined += 1;
            self.subst.insert(var.id, SubstRng::Done(simple_defn));
            self.simplify(*body)
          } else {
            let body = self.in_snapshot(|this| {
              this
                .in_scope
                .insert(var.id, Definition::BoundTo(simple_defn.clone(), occ));
              this.simplify(*body)
            });
            self.rebuild(IR::local(var, simple_defn, body))
          }
        }
      }
      IR::Var(v) => match self.subst.remove(&v.id) {
        Some(SubstRng::Suspend(ir, subst)) => {
          self.subst = subst;
          self.simplify(ir)
        }
        Some(SubstRng::Done(ir)) => {
          self.subst = Subst::default();
          self.simplify(ir)
        }
        None => match self.in_scope.get(&v.id) {
          None => panic!("ICE: Unbound variable encountered in simplification"),
          Some(Definition::BoundTo(ir, occ)) if self.should_inline(ir, *occ) => {
            self.subst = Subst::default();
            self.simplify(ir.clone())
          }
          Some(_) => self.rebuild(IR::Var(v)),
        },
      },
      IR::Int(i) => self.rebuild(IR::Int(i)),
    }
  }

  fn should_inline(&self, ir: &IR, occ: Occurrence) -> bool {
    match occ {
      Occurrence::Dead | Occurrence::Once => panic!("ICE: should_inline encountered unexpected dead or once occurrence. This should've been handled prior"),
      Occurrence::OnceInFun => ir.is_value() && self.some_benefit(ir),
      Occurrence::Many => ir.is_value() && self.should_inline_multi(ir),
    }
  }

  fn should_inline_multi(&self, ir: &IR) -> bool {
    ir.size() == 0 || (self.some_benefit(ir) && ir.size() <= self.inline_size_threshold)
  }

  fn did_no_work(&self) -> bool {
    self.saturated_fun_count == 0 && self.saturated_ty_fun_count == 0 && self.locals_inlined == 0
  }
}

pub fn simplify(ir: IR) -> IR {
  ir.within_toplevel_funs(|params, mut ir| {
    let in_scope: InScope = params
      .iter()
      .filter_map(|param| match param {
        Param::Val(var) => Some(var.id),
        Param::Ty(_) => None,
      })
      .map(|var| (var, Definition::Unknown))
      .collect();
    for _ in 0..4 {
      let (simple_ir, occs) = occurrence_analysis(ir);
      let mut simplifier = Simplifier::new(in_scope.clone(), occs);
      ir = simplifier.simplify(simple_ir);
      println!(
        "{}\n{}\n{}",
        simplifier.saturated_fun_count,
        simplifier.saturated_ty_fun_count,
        pretty_string(ir.clone(), 80)
      );
      if simplifier.did_no_work() {
        break;
      }
    }
    ir
  })
}

#[cfg(test)]
mod tests {
  use lowering_base::{lower, pretty::pretty_string};
  use types_base::{self as ast, type_infer, Ast};

  use super::*;

  fn simplify(ast: Ast<ast::Var>) -> IR {
    let (ast, scheme) = type_infer(ast).expect("Type checking failed");
    let (ir, _) = lower(ast, scheme);
    println!("{}", pretty_string(ir.clone(), 80));
    crate::simplify(ir)
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
  fn simple_removes_unused_vars() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let z = ast::Var(2);
    let ast = Ast::fun(x, locals([(y, Ast::Int(1)), (z, Ast::Int(2))], Ast::Var(x)));

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type]
          (fun [V0]
            V0))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_inline_once() {
    let y = ast::Var(0);
    let z = ast::Var(1);
    let ast = Ast::app(
      Ast::fun(y, Ast::app(Ast::Var(y), Ast::Int(157))),
      Ast::fun(z, Ast::Var(z)),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect!["157"];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_many_trivial_expression_is_inlined() {
    let x = ast::Var(0);
    let f = ast::Var(1);
    let ast = Ast::app(
      Ast::fun(
        x,
        Ast::fun(
          f,
          Ast::app(
            Ast::app(Ast::Var(f), Ast::Var(x)),
            Ast::app(Ast::app(Ast::Var(f), Ast::Var(x)), Ast::Var(x)),
          ),
        ),
      ),
      Ast::Int(3005),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (fun [V1]
          (V1 (3005 (V1 (3005 3005)))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_once_nontrivial_expression_is_inlined() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let f = ast::Var(2);

    let ast = Ast::fun(
      f,
      Ast::app(
        Ast::fun(x, Ast::app(Ast::Var(f), Ast::Var(x))),
        Ast::fun(y, Ast::app(Ast::Var(y), Ast::Int(3005))),
      ),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (fun [V0]
            (V0 (fun [V2] (V2 3005)))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_many_nontrivial_expression_is_not_inlined() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let f = ast::Var(2);

    let ast = Ast::app(
      Ast::fun(
        x,
        Ast::fun(f, Ast::app(Ast::app(Ast::Var(f), Ast::Var(x)), Ast::Var(x))),
      ),
      Ast::fun(y, Ast::app(Ast::Var(y), Ast::Int(3005))),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (let [(V0 (fun [V2] (V2 3005)))] (fun [V1] (V1 (V0 V0)))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }
}
