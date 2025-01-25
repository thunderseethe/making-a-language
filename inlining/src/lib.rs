
use lowering_items::{IR, ItemId};

enum Binder {
    Local(Var),
    Global(ItemId),
}
struct Occurrences {
}

fn occurrence_analysis(ir: IR) -> (IR, Occurrences) {
  fn occurrences(ir: IR, occ: &mut Occurrences) -> IR {
    match ir {
        IR::Var(var) => todo!(),
        IR::Int(_) => todo!(),
        IR::Fun(var, ir) => todo!(),
        IR::App(ir, ir1) => todo!(),
        IR::TyFun(kind, ir) => todo!(),
        IR::TyApp(ir, ty_app) => todo!(),
        IR::Tuple(vec) => todo!(),
        IR::Field(ir, _) => todo!(),
        IR::Tag(_, _, ir) => todo!(),
        IR::Case(_, ir, vec) => todo!(),
        IR::Item(_, item_id) => todo!(),
    }
  }
  let mut occurrences = Occurrences {};
  let ir_occurred = occurrences(ir, &mut occurrences);
}

fn inline(ir: IR) -> IR {
    todo!()
}

fn inlining(ir: IR) -> IR {
    todo!()
}

#[cfg(test)]
mod tests {
}
