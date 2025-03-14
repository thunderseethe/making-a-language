use std::any::Any;
use std::collections::HashMap;

use closure_convert_base::{Anf, Atom, Definition, DefinitionId, Locals};
use lowering_base::{Type, Var, VarId};
use wasm_encoder::{
  CodeSection, FuncType, Function, FunctionSection, Instruction, Module, Section, TableSection, TableType, TypeSection, ValType
};

#[derive(Default)]
struct EmitType {
  ty_sect: TypeSection,
  types: HashMap<FuncType, u32>,
}

impl EmitType {
  fn emit_func_ty(&mut self, func: FuncType) -> u32 {
    self.types.entry(func).or_insert_with_key(|func| {
      let indx = self.ty_sect.len();
      self.ty_sect.ty().func_type(func);
      indx
    })
  }
}

struct EmitWasm {
  types: EmitType,
  func: FunctionSection,
  code: CodeSection,
}

impl EmitWasm {

  fn emit_anf(&self, locals: &HashMap<VarId, u32>, anf: Anf) -> Vec<Instruction> {
    match anf {
      Anf::Atom(atom) => match atom {
        Atom::Var(var) => Instruction::LocalGet(locals[var]),
        Atom::Int(i) => Instruction::I32Const(i),
    },
      Anf::Closure(definition_id, vec) => {
        Instruction::RefFunc(todo!())
      },
      Anf::Apply(atom, vec) => todo!(),
      Anf::Access(var, _) => todo!(),
    }
  }

  fn emit_locals(&mut self, params: &[Var], body: Locals) -> Vec<Instruction> {
    let locals: HashMap<VarId, u32> = params
      .iter()
      .chain(body.binds.iter().map(|(var, _)| var))
      .enumerate()
      .map(|(local, var)| (var.id, local))
      .collect();
    for (var, defn) in body.binds {
      let inss = self.emit_anf(&locals, anf);
    }
  }

  fn emit_definition(&mut self, name: DefinitionId, definition: Definition) {
    definition.body
  }

}

pub fn emit_wasm(definitions: Vec<(DefinitionId, Definition)>) -> Module {
  let mut types = EmitType::default();
  let mut func = FunctionSection::new();
  let definitions: HashMap<DefinitionId, u32> = definitions.iter().map(|(defn_id, defn)| { 
    let id = types.emit_func_ty(ty);
    defn_id
  }).collect();
  let module = Module::default();
}

#[cfg(test)]
mod tests {
  use super::*;
}
