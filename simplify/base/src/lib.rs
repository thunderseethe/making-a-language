use std::collections::HashSet;

use im::HashMap;

use lowering_base::{Kind, Type, Var, VarId, IR};

enum Param {
  Ty(Kind),
  Val,
}

trait IRExt {
  fn is_trivial(&self) -> bool;

  fn is_value(&self) -> bool;

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

  fn split_funs(&self) -> (Vec<Param>, &IR) {
    fn split_funs<'a>(ir: &'a IR, params: &mut Vec<Param>) -> &'a IR {
      match ir {
        IR::TyFun(kind, ir) => {
          params.push(Param::Ty(*kind));
          split_funs(ir, params)
        }
        IR::Fun(_, ir) => {
          params.push(Param::Val);
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
  //ctx: Context,

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
    let (params, _) = ir.split_funs();
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

  fn rebuild(&mut self, ir: IR, in_scope: InScope, mut ctx: Context) -> IR {
    let Some((entry, subst)) = ctx.pop() else {
      return ir;
    };
    self.subst = subst;
    match entry {
      ContextEntry::App(arg) => {
        if let IR::Fun(var, body) = ir {
          self.saturated_fun_count += 1;
          let ir = IR::local(var, arg, *body);
          self.simplify(ir, in_scope, ctx)
        } else {
          let arg = self.simplify(arg, in_scope.clone(), vec![]);
          let app = IR::app(ir, arg);
          self.rebuild(app, in_scope, ctx)
        }
      }
      ContextEntry::TyApp(ty) => {
        let ir = if let IR::TyFun(_, body) = ir {
          self.saturated_ty_fun_count += 1;
          subst_ty(*body, ty)
        } else {
          IR::ty_app(ir, ty)
        };
        self.rebuild(ir, in_scope, ctx)
      }
      ContextEntry::Local(var, occ, body) => {
        if ir.is_trivial() {
          self.locals_inlined += 1;
          self.subst.insert(var.id, SubstRng::Done(ir));
          self.simplify(body, in_scope, ctx)
        } else {
          let body = self.simplify(body, in_scope.update(var.id, Definition::BoundTo(ir.clone(), occ)), vec![]);
          // We might have inlined all occurrences of var while simplifying body
          if let Occurrence::Dead = self.occs.lookup_var(&var) {
            self.rebuild(body, in_scope, ctx)
          } else {
            self.rebuild(IR::local(var, ir, body), in_scope, ctx)
          }
        }
      }
    }
  }

  fn simplify(&mut self, ir: IR, in_scope: InScope, mut ctx: Context) -> IR {
    match ir {
      IR::App(fun, arg) => {
        ctx.push((ContextEntry::App(*arg), self.subst.clone()));
        self.simplify(*fun, in_scope, ctx)
      }
      IR::TyApp(ty_fun, ty_app) => {
        ctx.push((ContextEntry::TyApp(ty_app), self.subst.clone()));
        self.simplify(*ty_fun, in_scope, ctx)
      }
      IR::TyFun(kind, body) => {
        let body = self.simplify(*body, in_scope.clone(), vec![]);
        self.rebuild(IR::ty_fun(kind, body), in_scope, ctx)
      }
      IR::Fun(var, body) => {
        let body = self.simplify(*body, in_scope.update(var.id, Definition::Unknown), vec![]);
        self.rebuild(IR::fun(var, body), in_scope, ctx)
      }
      IR::Local(var, defn, body) => {
        let occ = self.occs.lookup_var(&var);
        match occ {
          // Throwaway dead bindings.
          Occurrence::Dead => {
            self.locals_inlined += 1;
            self.simplify(*body, in_scope, ctx)
          }
          // Inline and remove bindings used once.
          Occurrence::Once => {
            self.locals_inlined += 1;
            let subst = self.subst.clone();
            self.subst.insert(var.id, SubstRng::Suspend(*defn, subst));
            self.simplify(*body, in_scope, ctx)
          }
          occ => {
            ctx.push((ContextEntry::Local(var, occ, *body), self.subst.clone()));
            self.simplify(*defn, in_scope, ctx)
          }
        }
      }
      IR::Var(v) => match self.subst.remove(&v.id) {
        Some(SubstRng::Suspend(ir, subst)) => {
          self.subst = subst;
          self.simplify(ir, in_scope, ctx)
        }
        Some(SubstRng::Done(ir)) => {
          self.subst = Subst::default();
          self.simplify(ir, in_scope, ctx)
        }
        None => match in_scope.get(&v.id) {
          None => panic!("ICE: Unbound variable encountered in simplification"),
          Some(Definition::BoundTo(ir, occ)) if self.should_inline(ir, *occ, &ctx) => {
            self.subst = Subst::default();
            // If we inlined a OnceInFun occurrence mark its binding as dead.
            // This prevents us from having to run more simplification passes to clean up dead
            // bindings
            if let Occurrence::OnceInFun = occ {
              self.occs.mark_dead(&v.id);
            }
            self.simplify(ir.clone(), in_scope, ctx)
          }
          Some(_) => self.rebuild(IR::Var(v), in_scope, ctx),
        },
      },
      IR::Int(i) => self.rebuild(IR::Int(i), in_scope, ctx),
    }
  }

  fn should_inline(&self, ir: &IR, occ: Occurrence, ctx: &Context) -> bool {
    match occ {
      Occurrence::Dead | Occurrence::Once => panic!("ICE: should_inline encountered unexpected dead or once occurrence. This should've been handled prior"),
      Occurrence::OnceInFun => ir.is_value() && self.some_benefit(ir, ctx),
      Occurrence::Many => ir.is_value() && self.should_inline_multi(ir, ctx),
    }
  }

  fn should_inline_multi(&self, ir: &IR, ctx: &Context) -> bool {
    ir.size() == 0 || (self.some_benefit(ir, ctx) && ir.size() <= self.inline_size_threshold)
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
  use types_base::{self as ast, type_infer, Ast};

  use super::*;

  fn simplify(ast: Ast<ast::Var>) -> IR {
    let (ast, scheme) = type_infer(ast).expect("Type checking failed");
    let (ir, _) = lower(ast, scheme);
    crate::simplify(ir)
  }

  fn make_vars<const N: usize>() -> [ast::Var; N] {
    let mut vars = [ast::Var(0); N];
    for (i, var) in vars.iter_mut().enumerate() {
      *var = ast::Var(i);
    }
    vars
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
    let [x, y, z] = make_vars();
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
    let [y, z] = make_vars();
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
    let [x, f] = make_vars();
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
          (V1 3005 (V1 3005 3005)))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_once_nontrivial_expression_is_inlined() {
    let [x, y, f] = make_vars();
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
    let [x, y, f] = make_vars();
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
          (let
            [(V0 (fun [V2] (V2 3005)))]
            (fun [V1]
              (V1 V0 V0))))"#]];
    expect.assert_eq(&pretty_string(ir, 80));
  }

  #[test]
  fn simple_onceinfun_uninteresting_context_is_not_inlined() {
    let [x, y, f] = make_vars();
    let ast = Ast::app(
      Ast::fun(f, Ast::fun(x, Ast::Var(f))),
      Ast::fun(y, Ast::app(Ast::Var(y), Ast::Int(3005))),
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
    let [x, y, w, f, g, h] = make_vars();
    // An interesting arg is any expression that isn't trivial.
    // We use a function for that purpose here.
    let interesting_arg = Ast::fun(g, Ast::Var(g));
    let ast = Ast::app(
      Ast::fun(f, Ast::fun(x, Ast::app(Ast::Var(f), interesting_arg))),
      Ast::fun(
        y,
        Ast::fun(w, Ast::app(Ast::Var(y), Ast::fun(h, Ast::Var(h)))),
      ),
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
    let [a, b, c, d, e, f, g, h, i, j, k, l, m] = make_vars();
    let ast = locals(
      [
        (
          a,
          locals(
            [(
              b,
              locals(
                [(
                  c,
                  locals([(d, locals([(e, Ast::Int(1))], Ast::Var(e)))], Ast::Var(d)),
                )],
                Ast::Var(c),
              ),
            )],
            Ast::Var(b),
          ),
        ),
        (i, Ast::Int(2)),
        (g, Ast::Int(3)),
        (h, Ast::Int(4)),
        (
          f,
          Ast::fun(j, Ast::fun(k, Ast::fun(l, Ast::fun(m, Ast::Var(j))))),
        ),
      ],
      Ast::app(
        Ast::app(
          Ast::app(Ast::app(Ast::Var(f), Ast::Var(a)), Ast::Var(i)),
          Ast::Var(g),
        ),
        Ast::Var(h),
      ),
    );

    let ir = simplify(ast);

    let expect = expect_test::expect!["1"];
    expect.assert_eq(&pretty_string(ir, 80));
  }
}
