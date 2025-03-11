use lowering_base::{IR, Type};
use simplify_base::subst_ty;

fn unwrap_forall(ir: IR, ty: Type) -> IR {
  let IR::TyFun(_, body) = ir else {
    panic!("ICE: Applied a type to a non type function IR in monomorph");
  };
  subst_ty(*body, ty)
}

pub fn monomorph(ir: IR, types: Vec<Type>) -> IR {
  types.into_iter().fold(ir, unwrap_forall)
}

#[cfg(test)]
mod tests {
  use super::*;
}
