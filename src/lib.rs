use closure_convert_base::{closure_convert, ItemId};
use desugar_base::{desugar, DesugarError};
use emit_base::emit_wasm;
use lowering_base::{self as ir, lower};
use monomorph_base::monomorph;
use name_resolution_base::{name_resolution, NameResolutionError};
use parser_base::parse;
use simplify_base::simplify;
use types_base::{type_infer, TypeError};

#[derive(Debug)]
pub enum CompileError {
  Desugar(DesugarError),
  NameResolution(NameResolutionError),
  Type(TypeError),
  Io(std::io::Error),
}
impl From<DesugarError> for CompileError {
  fn from(value: DesugarError) -> Self {
    Self::Desugar(value)
  }
}
impl From<NameResolutionError> for CompileError {
  fn from(value: NameResolutionError) -> Self {
    Self::NameResolution(value)
  }
}
impl From<TypeError> for CompileError {
  fn from(value: TypeError) -> Self {
    Self::Type(value)
  }
}
impl From<std::io::Error> for CompileError {
  fn from(value: std::io::Error) -> Self {
    Self::Io(value)
  }
}

fn trivial_monomorph(ir: ir::IR) -> ir::IR {
  let mut types = vec![];
  let mut fun = &ir;
  // Assume all types are Int.
  // This can't be wrong for base because we don't yet support any interesting types.
  // Any function getting passed around will use a function type not a
  while let ir::IR::TyFun(_, body) = fun {
    types.push(ir::Type::Int);
    fun = body;
  }
  monomorph(ir, types)
}

pub fn compile(input: &str) -> Result<Vec<u8>, CompileError> {
  let cst = parse(input);
  let unresolve_ast = desugar(input, cst)?;
  let untyped_ast = name_resolution(unresolve_ast)?;
  let (ast, scheme) = type_infer(untyped_ast)?;
  let (ir, _, _) = lower(ast, scheme);
  let closures = closure_convert(trivial_monomorph(simplify(ir)));

  let main_item = ItemId(
    closures
      .closure_items
      .last_key_value()
      .map(|(key, _)| key.0 + 1)
      .unwrap_or(0),
  );
  let mut items = closures.closure_items;
  items.insert(main_item, closures.item);

  Ok(emit_wasm(items.into_iter().collect()))
}
