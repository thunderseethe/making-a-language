use std::collections::HashMap;

use lowering_rows::{Branch, Row, TyApp, Type, Var, VarId, IR};

trait IRExt {
  fn is_trivial(&self) -> bool;

  fn is_value(&self) -> bool;

  fn count_args(&self) -> usize;
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
      IR::Tuple(elems) => elems.iter().all(|elem| elem.is_value()),
      IR::Field(ir, _) => ir.is_value(),
      IR::Tag(_, _, body) => body.is_value(),
      IR::App(_, _) | IR::Case(_, _, _) => false,
    }
  }

  fn count_args(&self) -> usize {
    match self {
      IR::Fun(_, _) => 1 + self.count_args(),
      IR::TyFun(_, _) => 1 + self.count_args(),
      _ => 0,
    }
  }
}

fn subst(haystack: IR, needle: Var, payload: IR) -> IR {
  match haystack {
    IR::Var(var) => {
      if var == needle {
        payload
      } else {
        IR::Var(var)
      }
    }
    IR::Int(i) => IR::Int(i),
    IR::Fun(var, ir) => IR::fun(var, subst(*ir, needle, payload)),
    IR::App(fun, arg) => IR::app(
      subst(*fun, needle.clone(), payload.clone()),
      subst(*arg, needle, payload),
    ),
    IR::TyFun(kind, ir) => IR::ty_fun(kind, subst(*ir, needle, payload)),
    IR::TyApp(ty_fun, ty) => IR::ty_app(subst(*ty_fun, needle, payload), ty),
    IR::Tuple(elems) => IR::tuple(
      elems
        .into_iter()
        .map(|elem| subst(elem, needle.clone(), payload.clone())),
    ),
    IR::Field(ir, indx) => IR::field(subst(*ir, needle, payload), indx),
    IR::Tag(ty, tag, ir) => IR::tag(ty, tag, subst(*ir, needle, payload)),
    IR::Case(ty, ir, branches) => IR::case(
      ty,
      subst(*ir, needle.clone(), payload.clone()),
      branches.into_iter().map(|branch| Branch {
        param: branch.param,
        body: subst(branch.body, needle.clone(), payload.clone()),
      }),
    ),
    IR::Local(var, defn, body) => IR::local(
      var,
      subst(*defn, needle.clone(), payload.clone()),
      subst(*body, needle, payload),
    ),
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
    IR::TyApp(ir, ty) => IR::ty_app(
      subst_ty(*ir, payload.clone()),
      match ty {
        TyApp::Ty(ty) => TyApp::Ty(ty.subst_ty(payload)),
        TyApp::Row(row) => TyApp::Row(row.subst_ty(payload)),
      },
    ),
    IR::Tuple(elems) => IR::tuple(
      elems
        .into_iter()
        .map(|elem| subst_ty(elem, payload.clone())),
    ),
    IR::Field(ir, indx) => IR::field(subst_ty(*ir, payload), indx),
    IR::Tag(ty, tag, ir) => IR::tag(ty.subst_ty(payload.clone()), tag, subst_ty(*ir, payload)),
    IR::Case(ty, ir, branches) => IR::case(
      ty.subst_ty(payload.clone()),
      subst_ty(*ir, payload.clone()),
      branches.into_iter().map(|branch| Branch {
        param: branch.param.map_ty(|ty| ty.subst_ty(payload.clone())),
        body: subst_ty(branch.body, payload.clone()),
      }),
    ),
    IR::Local(var, defn, body) => IR::local(
      var.map_ty(|ty| ty.subst_ty(payload.clone())),
      subst_ty(*defn, payload.clone()),
      subst_ty(*body, payload),
    ),
  }
}

fn subst_row(haystack: IR, payload: Row) -> IR {
  match haystack {
    IR::Var(var) => IR::Var(var.map_ty(|ty| ty.subst_row(payload))),
    IR::Int(i) => IR::Int(i),
    IR::Fun(var, ir) => IR::fun(
      var.map_ty(|ty| ty.subst_row(payload.clone())),
      subst_row(*ir, payload),
    ),
    IR::App(fun, arg) => IR::app(subst_row(*fun, payload.clone()), subst_row(*arg, payload)),
    IR::TyFun(kind, ir) => IR::ty_fun(kind, subst_row(*ir, payload)),
    IR::TyApp(ir, ty) => IR::ty_app(
      subst_row(*ir, payload.clone()),
      match ty {
        TyApp::Ty(ty) => TyApp::Ty(ty.subst_row(payload)),
        TyApp::Row(row) => TyApp::Row(row.subst_row(payload)),
      },
    ),
    IR::Tuple(elems) => IR::tuple(
      elems
        .into_iter()
        .map(|elem| subst_row(elem, payload.clone())),
    ),
    IR::Field(ir, indx) => IR::field(subst_row(*ir, payload), indx),
    IR::Tag(ty, tag, ir) => IR::tag(ty.subst_row(payload.clone()), tag, subst_row(*ir, payload)),
    IR::Case(ty, ir, branches) => IR::case(
      ty.subst_row(payload.clone()),
      subst_row(*ir, payload.clone()),
      branches.into_iter().map(|branch| Branch {
        param: branch.param.map_ty(|ty| ty.subst_row(payload.clone())),
        body: subst_row(branch.body, payload.clone()),
      }),
    ),
    IR::Local(var, defn, body) => IR::local(
      var.map_ty(|ty| ty.subst_row(payload.clone())),
      subst_row(*defn, payload.clone()),
      subst_row(*body, payload),
    ),
  }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Occurrence {
  Dead,
  Once,
  OnceInFun,
  ManyBranch,
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
            (Occurrence::Once, _)
            | (Occurrence::OnceInFun, _)
            | (_, Occurrence::Once)
            | (_, Occurrence::OnceInFun) => Occurrence::Many,
            (Occurrence::ManyBranch, Occurrence::ManyBranch) => Occurrence::Many,
          };
        })
        .or_insert(occ);
    }
  }

  fn merge_mut(&mut self, other: Self) {
    self.merge_internal(other, Occurrence::Many);
  }

  fn merge_in_branch_mut(&mut self, other: Self) {
    self.merge_internal(other, Occurrence::ManyBranch)
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
    IR::Tuple(elems) => {
      let mut tuple_occs = Occurrences::default();
      let tuple = IR::tuple(
        elems
          .into_iter()
          .map(occurrence_analysis)
          .map(|(elem, occs)| {
            tuple_occs.merge_mut(occs);
            elem
          }),
      );
      (tuple, tuple_occs)
    }
    IR::Field(ir, index) => {
      let (body, occs) = occurrence_analysis(*ir);
      (IR::field(body, index), occs)
    }
    IR::Tag(ty, tag, ir) => {
      let (body, occs) = occurrence_analysis(*ir);
      (IR::tag(ty, tag, body), occs)
    }
    IR::Case(ty, ir, branches) => {
      let (scrutinee, occs) = occurrence_analysis(*ir);
      let mut branch_occs = Occurrences::default();
      let case = IR::case(
        ty,
        scrutinee,
        branches.into_iter().map(|branch| {
          let (body, occs) = occurrence_analysis(branch.body);
          branch_occs.merge_in_branch_mut(occs);
          Branch {
            param: branch.param,
            body,
          }
        }),
      );
      (case, occs.merge(branch_occs))
    }
    IR::Local(var, defn, body) => {
      let (body, occs) = occurrence_analysis(*body);
      // Immediately strip away a dead binding.
      if let Occurrence::Dead = occs.lookup_var(&var) {
        (body, occs)
      } else {
        let (defn, defn_occs) = occurrence_analysis(*defn);
        (IR::local(var, defn, body), defn_occs)
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

#[derive(Default, Debug)]
struct Simplifier {
  // state to perform simplification
  occs: Occurrences,
  subst: Subst,
  in_scope: InScope,
  ctx: Context,

  // stats, used to determine if we simplified
  app_subst_count: usize,
  ty_app_subst_count: usize,
  tuple_field_count: usize,
  case_tag_count: usize,
}

#[derive(Debug)]
enum ContextEntry {
  AppContext(IR, Subst),
  TyAppContext(TyApp, Subst),
  FieldContext(usize, Subst),
  CaseContext(Type, Vec<Branch>, Subst),
}

type Context = Vec<ContextEntry>;

impl Simplifier {
  fn new(occs: Occurrences) -> Self {
    Self {
      occs,
      ..Default::default()
    }
  }

  fn some_benefit(&mut self, ir: &IR) -> bool {
    match ir {
      IR::TyFun(_, ir) => {
        let Some(entry @ ContextEntry::TyAppContext(_, _)) = self.ctx.pop() else {
          return false;
        };
        let result = self.some_benefit(ir);
        self.ctx.push(entry);
        result
      }
      IR::Fun(_, ir) => {
        let Some(ContextEntry::AppContext(arg, env)) = self.ctx.pop() else {
          return false;
        };
        // One of our args isn't trivial.
        if !arg.is_trivial() {
          self.ctx.push(ContextEntry::AppContext(arg, env));
          return true;
        } else {
          let result = self.some_benefit(ir);
          self.ctx.push(ContextEntry::AppContext(arg, env));
          result
        }
      }
      IR::Tag(_, _, _) => match self.ctx.last() {
        Some(ContextEntry::CaseContext(_, _, _)) => true,
        _ => false,
      },
      IR::Tuple(_) => match self.ctx.last() {
        Some(ContextEntry::FieldContext(_, _)) => true,
        _ => false,
      }
      _ => false,
    }
  }

  fn with_in_scope<T>(
    &mut self,
    var: VarId,
    defn: Definition,
    body: impl FnOnce(&mut Self) -> T,
  ) -> T {
    self.in_scope.insert(var, defn);
    let result = body(self);
    self.in_scope.remove(&var);
    result
  }

  fn rebuild(&mut self, mut ir: IR) -> IR {
    while let Some(cont) = self.ctx.pop() {
      match cont {
        ContextEntry::AppContext(arg, env) => {
          self.subst = env;
          ir = if let IR::Fun(var, body) = ir {
            self.simplify(IR::local(var, arg, *body))
          } else {
            let arg = self.simplify(arg);
            IR::app(ir, arg)
          };
        }
        ContextEntry::TyAppContext(ty_app, env) => {
          self.subst = env;
          ir = if let IR::TyFun(_, body) = ir {
            match ty_app {
              TyApp::Ty(ty) => subst_ty(*body, ty),
              TyApp::Row(row) => subst_row(*body, row),
            }
          } else {
            IR::ty_app(ir, ty_app)
          };
        }
        ContextEntry::FieldContext(index, env) => {
          self.subst = env;
          if let IR::Tuple(elems) = ir {
            ir = elems[index].clone();
          } else {
            ir = IR::field(ir, index);
          }
        }
        ContextEntry::CaseContext(ty, branches, env) => {
          self.subst = env;
          if let IR::Tag(_, indx, body) = ir {
            let branch = branches[indx].clone();
            ir = self.simplify(IR::local(branch.param, *body, branch.body));
          } else {
            let ctx = std::mem::take(&mut self.ctx);
            ir = IR::case(
              ty,
              ir,
              branches.into_iter().map(|branch| Branch {
                param: branch.param,
                body: self.simplify(branch.body),
              }),
            );
            self.ctx = ctx;
          }
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
      IR::Field(ir, indx) => {
        self
          .ctx
          .push(ContextEntry::FieldContext(indx, self.subst.clone()));
        self.simplify(*ir)
      }
      IR::Case(ty, ir, branches) => {
        self
          .ctx
          .push(ContextEntry::CaseContext(ty, branches, self.subst.clone()));
        self.simplify(*ir)
      }
      IR::Fun(var, body) => self.with_in_scope(var.id, Definition::Unknown, |this| {
        IR::fun(var, this.simplify(*body))
      }),
      IR::TyFun(kind, ir) => IR::ty_fun(kind, self.simplify(*ir)),
      IR::Tuple(elems) => IR::tuple(elems.into_iter().map(|elem| self.simplify(elem))),
      IR::Tag(ty, tag, ir) => {
        let tag = IR::tag(ty, tag, self.simplify(*ir));
        self.rebuild(tag)
      }
      IR::Local(var, defn, body) => {
        let occ = self.occs.lookup_var(&var);
        if let Occurrence::Once = occ {
          let subst = self.subst.clone();
          self.subst.insert(var.id, SubstRng::Suspend(*defn, subst));
          self.simplify(*body)
        } else {
          let simple_defn = self.simplify(*defn);
          if simple_defn.is_trivial() {
            self.subst.insert(var.id, SubstRng::Done(simple_defn));
            self.simplify(*body)
          } else {
            self
              .in_scope
              .insert(var.id, Definition::BoundTo(simple_defn.clone(), occ));
            let body = self.simplify(*body);
            IR::local(var, simple_defn, body)
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
            todo!()
          }
          Some(_) => IR::Var(v),
          None => todo!(),
        },
      },
      IR::Int(i) => IR::Int(i),
    }
  }

  fn should_inline(&mut self, ir: &IR, occ: Occurrence) -> bool {
    match occ {
      Occurrence::Dead | Occurrence::Once => panic!("ICE: should_inline encountered unexpected dead or once occurrence. This should've been handled prior"),
      Occurrence::OnceInFun => ir.is_value() && self.some_benefit(ir),
      Occurrence::ManyBranch => todo!(),
      Occurrence::Many => todo!()
    }
  }

  fn did_no_work(&self) -> bool {
    self.app_subst_count == 0
      && self.ty_app_subst_count == 0
      && self.tuple_field_count == 0
      && self.case_tag_count == 0
  }
}

fn simplify(ir: IR) -> IR {
  let mut ir = ir;
  for _ in 0..4 {
    let (simple_ir, occs) = occurrence_analysis(ir);
    let mut simplifier = Simplifier::new(occs);
    ir = simplifier.simplify(simple_ir);
    if simplifier.did_no_work() {
      break;
    }
  }
  ir
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn simple_herp() {}
}
