use std::default;

use lowering_base::{Type, Var, IR};

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
  }
}

#[derive(Default, Debug)]
struct Simplifier {
  app_subst_count: usize,
  ty_app_subst_count: usize,
}

impl Simplifier {
  fn simplify(&mut self, ir: IR) -> IR {
    match ir {
      IR::App(fun, arg) => {
        let IR::Fun(var, body) = *fun else {
          return IR::app(self.simplify(*fun), self.simplify(*arg));
        };
        self.app_subst_count += 1;
        subst(*body, var, *arg)
      }
      IR::TyApp(ty_fun, ty) => {
        let IR::TyFun(_, body) = *ty_fun else {
          return IR::ty_app(self.simplify(*ty_fun), ty);
        };
        self.ty_app_subst_count += 1;
        subst_ty(*body, ty)
      }
      IR::Fun(var, body) => IR::fun(var, self.simplify(*body)),
      IR::TyFun(kind, ir) => IR::ty_fun(kind, self.simplify(*ir)),
      ir => ir,
    }
  }

  fn did_no_work(&self) -> bool {
    self.app_subst_count == 0 && self.ty_app_subst_count == 0
  }
}

fn simplify(ir: IR) -> IR {
  let mut ir = ir;
  for _ in 0..4 {
    let mut simplifier = Simplifier::default();
    ir = simplifier.simplify(ir);
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
