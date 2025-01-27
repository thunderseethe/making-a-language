use std::collections::HashMap;

use lowering_items::{ItemId, VarId, IR};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum Occurrence {
  Dead,
  Once,
  OnceInFun,
  ManyBranch,
  Many,
}

#[derive(Default)]
struct Occurrences {
  vars: HashMap<VarId, Occurrence>,
  items: HashMap<ItemId, Occurrence>,
}
impl Occurrences {
  fn once_var(var: VarId) -> Self {
    let mut vars = HashMap::default();
    vars.insert(var, Occurrence::Once);
    Self {
      vars,
      ..Default::default()
    }
  }

  fn once_item(item: ItemId) -> Self {
    let mut items = HashMap::default();
    items.insert(item, Occurrence::Once);
    Self {
      items,
      ..Default::default()
    }
  }

  fn in_fun(self) -> Self {
    Self {
      vars: self
        .vars
        .into_iter()
        .map(|(var_id, occ)| {
          (
            var_id,
            match occ {
              Occurrence::Once => Occurrence::OnceInFun,
              occ => occ,
            },
          )
        })
        .collect(),
      items: self
        .items
        .into_iter()
        .map(|(item_id, occ)| {
          (
            item_id,
            match occ {
              Occurrence::Once => Occurrence::OnceInFun,
              occ => occ,
            },
          )
        })
        .collect(),
    }
  }

  fn merge(mut self, other_occs: Self) -> Self {
      fn merge(left: Occurrence, right: Occurrence) -> Occurrence {
          match (left, right) {
              (Occurrence::Once, Occurrence::Once) => Occurrence::Many,
              (left, _) => left
          }
      }
      for (var_id, occ) in other_occs.vars {
        self.vars.entry(var_id)
            .and_modify(|in_place_occ| {
                *in_place_occ = merge(*in_place_occ, occ);
            })
            .or_insert(occ);
      }
      for (item_id, occ) in other_occs.items {
        self.items.entry(item_id)
            .and_modify(|in_place_occ| {
                *in_place_occ = merge(*in_place_occ, occ);
            })
            .or_insert(occ);
      }
      self
  }
}

fn occurrence_analysis(ir: IR) -> (IR, Occurrences) {
  fn occurrences(ir: IR) -> (IR, Occurrences) {
    match ir {
      IR::Var(var) => {
        let occurrences = Occurrences::once_var(var.id);
        (IR::Var(var), occurrences)
      }
      IR::Item(ty, item_id) => (IR::Item(ty, item_id), Occurrences::once_item(item_id)),
      IR::Int(i) => (IR::Int(i), Occurrences::default()),
      IR::Fun(var, body) => {
        let (body, occs) = occurrences(*body);
        (IR::fun(var, body), occs.in_fun())
      }
      IR::App(fun, arg) => {
        let (fun, fun_occs) = occurrences(*fun);
        let (arg, arg_occs) = occurrences(*arg);
        (IR::app(fun, arg), fun_occs.merge(arg_occs))
      }
      IR::TyFun(kind, ir) => todo!(),
      IR::TyApp(ir, ty_app) => todo!(),
      IR::Tuple(vec) => todo!(),
      IR::Field(ir, _) => todo!(),
      IR::Tag(_, _, ir) => todo!(),
      IR::Case(_, ir, vec) => todo!(),
    }
  }
  occurrences(ir)
}

fn inline(ir: IR) -> IR {
  todo!()
}

fn inlining(ir: IR) -> IR {
  todo!()
}

#[cfg(test)]
mod tests {}
