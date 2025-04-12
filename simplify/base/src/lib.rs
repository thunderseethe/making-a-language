use im::HashMap;
use std::collections::HashSet;
use std::ops::ControlFlow;

use lowering_base::{Kind, Type, Var, VarId, IR};

pub enum Param {
  Ty(Kind),
  Val(Var),
}

pub trait IRExt {
  fn is_trivial(&self) -> bool;

  fn is_value(&self) -> bool;

  fn split_funs(self) -> (Vec<Param>, IR);

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

  fn split_funs(self) -> (Vec<Param>, IR) {
    fn split_funs(ir: IR, params: &mut Vec<Param>) -> IR {
      match ir {
        IR::TyFun(kind, ir) => {
          params.push(Param::Ty(kind));
          split_funs(*ir, params)
        }
        IR::Fun(var, ir) => {
          params.push(Param::Val(var));
          split_funs(*ir, params)
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

pub fn subst_ty(haystack: IR, payload: Type) -> IR {
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

#[derive(Default, Debug, Clone)]
struct Occurrences {
  vars: HashMap<VarId, Occurrence>,
}
impl Occurrences {
  fn with_var_once(var: VarId) -> Self {
    let mut vars = HashMap::default();
    vars.insert(var, Occurrence::Once);
    Self { vars }
  }

  fn in_fun(self, free: &HashSet<VarId>) -> Self {
    Self {
      vars: self
        .vars
        .into_iter()
        .map(|(id, occ)| {
          (
            id,
            match occ {
              // Only mark the free variables of a function as OnceInFun.
              // This prevents marking bindings fully encapsulated by the function as OnceInFun.
              // In term:
              // (fun [V0] (let [V1 3] V1))
              // V1 should be considered Once not OnceInFun.
              Occurrence::Once if free.contains(&id) => Occurrence::OnceInFun,
              occ => occ,
            },
          )
        })
        .collect(),
    }
  }

  fn merge(mut self, other: Self) -> Self {
    let once_meet = Occurrence::Many;
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
    self
  }

  fn lookup_var(&self, var: &Var) -> Occurrence {
    self.vars.get(&var.id).copied().unwrap_or(Occurrence::Dead)
  }

  fn mark_dead(&mut self, id: &VarId) {
    self.vars.remove(id);
  }
}

fn occurrence_analysis(ir: &IR) -> (HashSet<VarId>, Occurrences) {
  match ir {
    IR::Var(var) => {
      let mut free = HashSet::default();
      free.insert(var.id);
      (free, Occurrences::with_var_once(var.id))
    }
    IR::Int(_) => (HashSet::default(), Occurrences::default()),
    IR::Fun(var, ir) => {
      let (mut free, occs) = occurrence_analysis(ir);
      free.remove(&var.id);
      let occs = occs.in_fun(&free);
      (free, occs)
    }
    IR::App(fun, arg) => {
      let (mut fun_free, fun_occs) = occurrence_analysis(fun);
      let (arg_free, arg_occs) = occurrence_analysis(arg);
      fun_free.extend(arg_free);
      (fun_free, fun_occs.merge(arg_occs))
    }
    IR::TyFun(_, ir) => occurrence_analysis(ir),
    IR::TyApp(ir, _) => occurrence_analysis(ir),
    IR::Local(var, defn, body) => {
      let (mut free, occs) = occurrence_analysis(body);
      let (defn_free, defn_occs) = occurrence_analysis(defn);
      free.extend(defn_free);
      free.remove(&var.id);
      (free, defn_occs.merge(occs))
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

#[derive(Debug, Clone)]
struct Simplifier {
  // state to perform simplification
  occs: Occurrences,
  subst: Subst,

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
      saturated_fun_count: Default::default(),
      saturated_ty_fun_count: Default::default(),
      locals_inlined: Default::default(),
    }
  }
}

#[derive(Debug, Clone)]
enum ContextEntry {
  App(IR),
  TyApp(Type),
  Local(Var, Occurrence, IR),
}

type Context = Vec<(ContextEntry, Subst)>;

impl Simplifier {
  fn new(occs: Occurrences) -> Self {
    Self {
      occs,
      ..Default::default()
    }
  }

  fn some_benefit(&self, ir: &IR, ctx: &Context) -> bool {
    let (params, _) = ir.clone().split_funs();
    // If we have a non trivial argument in context, there's some benefit.
    if ctx
      .iter()
      .rev()
      .take(params.len())
      .any(|entry| match entry {
        (ContextEntry::App(arg), _) => !arg.is_trivial(),
        _ => false,
      })
    {
      return true;
    }

    // We have enough arguments to saturate our parameters.
    // We know this is a local function so there is benefit to inline
    if ctx.len() > params.len() {
      return true;
    }

    // If we saturate all args to our function and then apply more args to the body there is value
    // in inlining.
    matches!(ctx.get(params.len()), Some((ContextEntry::App(_), _)))
  }

  fn rebuild(&mut self, mut ir: IR, in_scope: InScope, mut ctx: Context) -> IR {
    while let Some((entry, subst)) = ctx.pop() {
      self.subst = subst;
      match entry {
        ContextEntry::App(arg) => {
          if let IR::Fun(var, body) = ir {
            self.saturated_fun_count += 1;
            return self.simplify(IR::local(var, arg, *body), in_scope, ctx);
          } else {
            let arg = self.simplify(arg, in_scope.clone(), vec![]);
            ir = IR::app(ir, arg);
          }
        }
        ContextEntry::TyApp(ty) => {
          ir = if let IR::TyFun(_, body) = ir {
            self.saturated_ty_fun_count += 1;
            subst_ty(*body, ty)
          } else {
            IR::ty_app(ir, ty)
          }
        }
        ContextEntry::Local(var, occ, body) => {
          if ir.is_trivial() {
            self.locals_inlined += 1;
            self.subst.insert(var.id, SubstRng::Done(ir));
            return self.simplify(body, in_scope, ctx);
          } else {
            let body = self.simplify(
              body,
              in_scope.update(var.id, Definition::BoundTo(ir.clone(), occ)),
              vec![],
            );
            // We might have inlined all occurrences of var while simplifying body.
            // If our binding is now dead, remove it.
            ir = if let Occurrence::Dead = self.occs.lookup_var(&var) {
              body
            } else {
              IR::local(var, ir, body)
            };
          }
        }
      }
    }
    ir
  }

  fn simplify(&mut self, mut ir: IR, in_scope: InScope, mut ctx: Context) -> IR {
    loop {
      ir = match ir {
        IR::App(fun, arg) => {
          ctx.push((ContextEntry::App(*arg), self.subst.clone()));
          *fun
        }
        IR::TyApp(ty_fun, ty_app) => {
          ctx.push((ContextEntry::TyApp(ty_app), self.subst.clone()));
          *ty_fun
        }
        IR::Int(i) => break self.rebuild(IR::Int(i), in_scope, ctx),
        IR::TyFun(kind, body) => {
          let body = self.simplify(*body, in_scope.clone(), vec![]);
          break self.rebuild(IR::ty_fun(kind, body), in_scope, ctx);
        }
        IR::Fun(var, body) => {
          let body = self.simplify(*body, in_scope.update(var.id, Definition::Unknown), vec![]);
          break self.rebuild(IR::fun(var, body), in_scope, ctx);
        }
        IR::Local(var, defn, body) => self.simplify_local(var, *defn, *body, &mut ctx),
        IR::Var(var) => match self.simplify_var(var, in_scope.clone(), &ctx) {
          ControlFlow::Continue(ir) => ir,
          ControlFlow::Break(var) => break self.rebuild(IR::Var(var), in_scope, ctx),
        },
      }
    }
  }

  fn simplify_local(&mut self, var: Var, defn: IR, body: IR, ctx: &mut Context) -> IR {
    match self.occs.lookup_var(&var) {
      // Throwaway dead bindings.
      Occurrence::Dead => {
        self.locals_inlined += 1;
        body
      }
      // Inline and remove locals used once.
      Occurrence::Once => {
        self.locals_inlined += 1;
        let subst = self.subst.clone();
        self.subst.insert(var.id, SubstRng::Suspend(defn, subst));
        body
      }
      occ => {
        ctx.push((ContextEntry::Local(var, occ, body), self.subst.clone()));
        defn
      }
    }
  }

  fn simplify_var(&mut self, var: Var, in_scope: InScope, ctx: &Context) -> ControlFlow<Var, IR> {
    match self.subst.remove(&var.id) {
      Some(SubstRng::Suspend(payload, subst)) => {
        self.subst = subst;
        ControlFlow::Continue(payload)
      }
      Some(SubstRng::Done(payload)) => {
        self.subst = Subst::default();
        ControlFlow::Continue(payload)
      }
      None => self.callsite_inline(var, in_scope, ctx),
    }
  }

  fn callsite_inline(
    &mut self,
    var: Var,
    in_scope: InScope,
    ctx: &Context,
  ) -> ControlFlow<Var, IR> {
    in_scope
      .get(&var.id)
      .map(|bind| match bind {
        Definition::BoundTo(payload, occ) if self.should_inline(payload, *occ, ctx) => {
          self.subst = Subst::default();
          // If we inlined a OnceInFun occurrence, mark its binding as dead.
          // This prevents us from having to run more simplification passes to clean up dead
          // bindings
          if let Occurrence::OnceInFun = occ {
            self.occs.mark_dead(&var.id);
          }
          ControlFlow::Continue(payload.clone())
        }
        _ => ControlFlow::Break(var),
      })
      .expect("ICE: Unbound variable encountered in simplification")
  }

  fn should_inline(&self, ir: &IR, occ: Occurrence, ctx: &Context) -> bool {
    match occ {
      Occurrence::Dead | Occurrence::Once => panic!("ICE: should_inline encountered unexpected dead or once occurrence. This should've been handled prior"),
      Occurrence::OnceInFun => ir.is_value() && self.some_benefit(ir, ctx),
      Occurrence::Many => {
          let size = ir.size();
          let no_size_increase = size == 0;
          let small_enough = size <= self.inline_size_threshold;
          ir.is_value()
          && (no_size_increase
                || (small_enough && self.some_benefit(ir, ctx)))
      },
    }
  }

  fn did_no_work(&self) -> bool {
    self.saturated_fun_count == 0 && self.saturated_ty_fun_count == 0 && self.locals_inlined == 0
  }
}

pub fn simplify(mut ir: IR) -> IR {
  for _ in 0..2 {
    let (_, occs) = occurrence_analysis(&ir);
    let mut simplifier = Simplifier::new(occs);
    ir = simplifier.simplify(ir, InScope::default(), vec![]);
    if simplifier.did_no_work() {
      break;
    }
  }
  ir
}

#[cfg(test)]
mod tests {
  use lowering_base::{lower, pretty::pretty_string};
  use types_base::builder::{make_vars, AstBuilder};
  use types_base::{self as ast, type_infer, Ast};

  use super::*;

  fn simplify(ast: Ast<ast::Var>) -> IR {
    let (ast, scheme) = type_infer(ast).expect("Type checking failed");
    let (ir, _, _) = lower(ast, scheme);
    crate::simplify(ir)
  }

  #[test]
  fn simple_removes_unused_vars() {
    let b = AstBuilder::default();
    let [x, y, z] = make_vars();
    let ast = b.fun(x, b.locals([(y, b.int(1)), (z, b.int(2))], b.var(x)));

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type]
          (fun [V0]
            V0))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_inline_once() {
    let b = AstBuilder::default();
    let [y, z] = make_vars();
    let ast = b.app(b.fun(y, b.app(b.var(y), b.int(157))), b.fun(z, b.var(z)));

    let ir = simplify(ast);

    let expect = expect_test::expect!["157"];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_many_trivial_expression_is_inlined() {
    let b = AstBuilder::default();
    let ast = b.app(
      b.make_funs(|[x, f]| {
        b.app(
          b.app(b.var(f), b.var(x)),
          b.apps(b.var(f), [b.var(x), b.var(x)]),
        )
      }),
      b.int(3005),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (fun [V1]
          (V1 3005 (V1 3005 3005)))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_once_nontrivial_expression_is_inlined() {
    let [x, y, f] = make_vars();
    let b = AstBuilder::default();
    let ast = b.fun(
      f,
      b.app(
        b.fun(x, b.app(b.var(f), b.var(x))),
        b.fun(y, b.app(b.var(y), b.int(3005))),
      ));

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (fun [V0]
            (V0 (fun [V2] (V2 3005)))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_many_nontrivial_expression_is_not_inlined() {
    let b = AstBuilder::default();
    let [x, y, f] = make_vars();
    let ast = b.app(
      b.fun(
        x,
        b.fun(f, b.app(b.app(b.var(f), b.var(x)), b.var(x))),
      ),
      b.fun(y, b.app(b.var(y), b.int(3005))),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (let
            [(V0 (fun [V2] (V2 3005)))]
            (fun [V1]
              (V1 V0 V0))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_onceinfun_uninteresting_context_is_not_inlined() {
    let b = AstBuilder::default();
    let [x, y, f] = make_vars();
    let ast = b.app(
      b.funs([f, x], b.var(f)),
      b.fun(y, b.app(b.var(y), b.int(3005))),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type]
          (let
            [(V0 (fun [V2] (V2 3005)))]
            (fun [V1]
              V0)))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_onceinfun_interesting_arg_is_inlined() {
    let b = AstBuilder::default();
    let [x, y, w, f, g, h] = make_vars();
    // An interesting arg is any expression that isn't trivial.
    // We use a function for that purpose here.
    let interesting_arg = b.fun(g, b.var(g));
    let ast = b.app(
      b.funs([f, x], b.app(b.var(f), interesting_arg)),
      b.funs([y, w], b.app(b.var(y), b.fun(h, b.var(h)))),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect![[r#"
        (ty_fun [Type Type Type]
          (fun [V1, V4, V5]
            V5))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_big_expr() {
    let build = AstBuilder::default();
    let [a, b, c, d, e, f, g, h, i, j, k, l, m] = make_vars();
    let ast = build.locals(
      [
        (
          a,
          build.locals(
            [(
              b,
              build.locals(
                [(
                  c,
                  build.locals([(d, build.locals([(e, build.int(1))], build.var(e)))], build.var(d)),
                )],
                build.var(c),
              ),
            )],
            build.var(b),
          ),
        ),
        (i, build.int(2)),
        (g, build.int(3)),
        (h, build.int(4)),
        (
          f,
          build.funs([j, k, l, m], build.var(j)),
        ),
      ],
      build.apps(
        build.var(f),
        [ build.var(a)
        , build.var(i)
        , build.var(g)
        , build.var(h)
        ]
      ));

    let ir = simplify(ast);

    let expect = expect_test::expect!["1"];
    expect.assert_eq(&pretty_string(ir, 80));
  }
}
