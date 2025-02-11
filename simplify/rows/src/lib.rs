use lowering_rows::{Branch, Kind, Row, TyApp, Type, Var, IR};

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
    IR::Tuple(elems) => todo!(),
    IR::Field(ir, indx) => todo!(),
    IR::Tag(_, _, ir) => todo!(),
    IR::Case(_, ir, vec) => todo!(),
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
  }
}

#[derive(Default, Debug)]
struct Simplifier {
  app_subst_count: usize,
  ty_app_subst_count: usize,
  tuple_field_count: usize,
  case_tag_count: usize,
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
      IR::TyApp(ty_fun, ty_app) => {
        let IR::TyFun(kind, body) = *ty_fun else {
          return IR::ty_app(self.simplify(*ty_fun), ty_app);
        };
        self.ty_app_subst_count += 1;
        match (kind, ty_app) {
          (Kind::Type, TyApp::Ty(ty)) => subst_ty(*body, ty),
          (Kind::Row, TyApp::Row(row)) => subst_row(*body, row),
          _ => panic!("ICE: Kind mismatch. TyApp has wrong argument for its node."),
        }
      }
      IR::Field(ir, indx) => {
        let IR::Tuple(elems) = *ir else {
          return IR::field(simplify(*ir), indx);
        };
        self.tuple_field_count += 1;
        elems[indx].clone()
      },
      IR::Case(ty, ir, branches) => {
        let IR::Tag(ty, tag, body) = *ir else {
            return IR::case(ty, simplify(*ir), branches.into_iter().map(|branch| {
              Branch {
                param: branch.param,
                body: simplify(branch.body),
              }
            }));
        };
        self.case_tag_count += 1;
        let branch = branches[tag].clone();
        todo!()
      },
      IR::Fun(var, body) => IR::fun(var, self.simplify(*body)),
      IR::TyFun(kind, ir) => IR::ty_fun(kind, self.simplify(*ir)),
      IR::Tuple(elems) => IR::tuple(elems.into_iter().map(simplify)),
      IR::Tag(ty, tag, ir) => IR::tag(ty, tag, simplify(*ir)),
      IR::Var(var) => todo!(),
      IR::Int(_) => todo!(),
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
