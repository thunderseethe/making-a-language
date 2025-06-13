use lowering_base::{IR, Type};

fn instantiate(ir: IR, types: Vec<Type>) -> IR {
  types.into_iter().fold(ir, |ir, ty| {
    let IR::TyFun(_, body) = ir else {
      panic!("ICE: Applied a type to a non type function IR in monomorph");
    };
    simplify_base::subst_ty(*body, ty)
  })
}

// At this stage we don't really have enough information to do proper monomorphization.
// Notably we don't have top level functions or a concept of a main function.
// Instead of performing real monomorphization, we assume all unsolved type variables are Int.
//
// This only works because we lack top level functions. We'll never encounter a case where we want
// to instantiate a type variable with a function. We also only have one base type, so we're safe
// to assume all unsolve variables are that type (Int).
pub fn trivial_monomorph(ir: IR) -> IR {
  let mut types = vec![];
  let mut fun = &ir;
  // Assume all types are Int.
  // This can't be wrong for base because we don't yet support any interesting types.
  // Any function getting passed around will use a function type not a
  while let IR::TyFun(_, body) = fun {
    types.push(Type::Int);
    fun = body;
  }
  instantiate(ir, types)
}
