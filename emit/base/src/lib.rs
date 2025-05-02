use std::collections::{HashMap, HashSet};
use std::ops::Index;

use closure_convert_base::{Item, ItemId, Type, Var, VarId, IR};
use lowering_base::pretty::pretty_string;
use wasm_encoder::{
  AbstractHeapType, CodeSection, CompositeInnerType, CompositeType, ExportKind, ExportSection,
  FieldType, FuncType, Function, FunctionSection, HeapType, Instruction, Module,
  RefType, StorageType, StructType, SubType, TypeSection, ValType,
};

#[derive(Eq, Hash, PartialEq)]
enum WasmTy {
  Func(FuncType),
  Struct(Vec<FieldType>, bool),
}

fn abstract_struct_ty() -> ValType {
  ValType::Ref(RefType {
    nullable: false,
    heap_type: HeapType::Abstract {
      shared: false,
      ty: AbstractHeapType::Struct,
    },
  })
}

trait AsValTy {
  fn as_val_ty(&self) -> ValType;
}
impl AsValTy for u32 {
  fn as_val_ty(&self) -> ValType {
    ValType::Ref(RefType {
      nullable: false,
      heap_type: HeapType::Concrete(*self),
    })
  }
}

struct ClosureTypeIndex {
  func_index: u32,
  struct_index: u32,
}

#[derive(Default)]
struct EmitType {
  types: Vec<WasmTy>,
  supertypes: HashMap<u32, u32>,
}

impl EmitType {
  fn into_type_section(self) -> TypeSection {
    let mut sect = TypeSection::new();
    let supertype_set = self.supertypes.values().copied().collect::<HashSet<_>>();
    for (i, ty) in self.types.into_iter().enumerate() {
      let indx: u32 = i.try_into().unwrap();
      let supertype_idx = self.supertypes.get(&indx).copied();
      let (inner, is_final) = match ty {
        WasmTy::Func(func_type) => (
          CompositeInnerType::Func(func_type),
          !supertype_set.contains(&indx),
        ),
        WasmTy::Struct(fields, is_final) => (
          CompositeInnerType::Struct(StructType {
            fields: fields.into_boxed_slice(),
          }),
          is_final,
        ),
      };
      sect.ty().subtype(&SubType {
        is_final,
        supertype_idx,
        composite_type: CompositeType {
          shared: false,
          inner,
        },
      })
    }
    sect
  }

  fn emit_ref_ty(&mut self, key: WasmTy) -> u32 {
    self
      .types
      .iter()
      .position(|x| x == &key)
      .unwrap_or_else(|| {
        let indx = self.types.len();
        self.types.push(key);
        indx
      })
      .try_into()
      .unwrap()
  }

  fn emit_closure_index(&mut self, arg: &Type, ret: &Type) -> ClosureTypeIndex {
    let arg_valty = self.emit_val_ty(arg);
    let ret_valty = self.emit_val_ty(ret);

    let func_index = self.emit_ref_ty(WasmTy::Func(FuncType::new(
      [abstract_struct_ty(), arg_valty],
      [ret_valty],
    )));
    let struct_index = self.emit_ref_ty(WasmTy::Struct(
      vec![FieldType {
        element_type: StorageType::Val(ValType::Ref(RefType {
          nullable: false,
          heap_type: HeapType::Concrete(func_index),
        })),
        mutable: false,
      }],
      false,
    ));

    ClosureTypeIndex {
      func_index,
      struct_index,
    }
  }

  fn emit_closure_env_index(&mut self, closure: &Type, env: &[Type]) -> u32 {
    let Type::Closure(arg, ret) = closure else {
      panic!("ICE: Non-closure type appeared in ClosureEnv type");
    };

    let closure_indices = self.emit_closure_index(arg, ret);
    let code_field = FieldType {
      element_type: StorageType::Val(closure_indices.func_index.as_val_ty()),
      mutable: false,
    };
    let super_indx = self.emit_ref_ty(WasmTy::Struct(vec![code_field], false));
    let fields = std::iter::once(code_field)
      .chain(env.iter().map(|ty| FieldType {
        element_type: StorageType::Val(self.emit_val_ty(ty)),
        mutable: false,
      }))
      .collect();

    let struct_idx = self.emit_ref_ty(WasmTy::Struct(fields, true));
    self.supertypes.insert(struct_idx, super_indx);
    struct_idx
  }

  fn emit_val_ty(&mut self, ty: &Type) -> ValType {
    match ty {
      Type::I32 => ValType::I32,
      Type::Closure(arg, ret) => self.emit_closure_index(arg, ret).struct_index.as_val_ty(),
      Type::ClosureEnv(closure, _) => self.emit_val_ty(closure),
    }
  }

  fn emit_item_ty(&mut self, item: &Item) -> u32 {
    let ret_ty = match &item.ret_ty {
      Type::Closure(_, _) => abstract_struct_ty(),
      ty => self.emit_val_ty(ty),
    };
    let func_ty = FuncType::new(
      item.params.iter().map(|var|
          // For definition parameters we need to handle closure environment parameters specially.
          // We erase closures to be of type `(ref struct)` when passing them, so we need to emit a
          // `(ref struct)` as the type of any closure env parameters we see.
          match &var.ty {
            Type::ClosureEnv(_, _) => abstract_struct_ty(),
            ty => self.emit_val_ty(ty),
          }),
      [ret_ty],
    );
    self.emit_ref_ty(WasmTy::Func(func_ty))
  }
}

/*
struct EmitWasm {
  types: EmitType,
  func: FunctionSection,
  functions: HashMap<DefinitionId, u32>,
  code: CodeSection,
}

impl EmitWasm {
  fn emit_anf(
    &mut self,
    locals: &HashMap<VarId, (u32, ValType)>,
    ty: &Type,
    anf: Anf,
  ) -> Vec<Instruction<'static>> {
    match anf {
      Anf::Atom(atom) => match atom {
        Atom::Var(var) => vec![Instruction::LocalGet(locals[&var.id].0)],
        Atom::Int(i) => vec![Instruction::I32Const(i.try_into().unwrap())],
      },
      Anf::Closure(definition_id, vars) => {
        // This is not the function type, what am I doing??
        let func_indx = self.functions[&definition_id];
        let struct_idx = self
          .types
          .emit_closure_env_index(ty, &vars.iter().map(|v| v.ty.clone()).collect::<Vec<_>>());
        let ValType::Ref(RefType { heap_type, .. }) = self.types.emit_val_ty(ty) else {
          panic!("ICE: Closure assigned to variable with non closure type");
        };
        let mut ins = vec![Instruction::RefFunc(func_indx)];
        ins.extend(
          vars
            .into_iter()
            .map(|var| Instruction::LocalGet(locals[&var.id].0)),
        );
        ins.push(Instruction::StructNew(struct_idx));
        ins.push(Instruction::RefCastNonNull(heap_type));
        ins
      }
      Anf::Apply(var, atom) => {
        let local_idx = locals[&var.id].0;
        let Type::Closure(arg, ret) = &var.ty else {
          panic!("ICE: Expected clsoure type for function of apply");
        };
        let closure_indices = self.types.emit_closure_index(arg, ret);
        vec![
          Instruction::LocalGet(local_idx),
          match atom {
            Atom::Var(var) => Instruction::LocalGet(locals[&var.id].0),
            Atom::Int(i) => Instruction::I32Const(i.try_into().unwrap()),
          },
          Instruction::LocalGet(local_idx),
          Instruction::StructGet {
            struct_type_index: closure_indices.struct_index,
            field_index: 0,
          },
          Instruction::CallRef(closure_indices.func_index),
        ]
      }
      Anf::Access(var, field_index) => {
        let local = locals[&var.id];
        let ValType::Ref(RefType {
          heap_type: HeapType::Concrete(struct_type_index),
          ..
        }) = local.1
        else {
          panic!("ICE: Struct access contained non struct variable.");
        };

        vec![
          Instruction::LocalGet(local.0),
          Instruction::StructGet {
            struct_type_index,
            // Our struct includes a code field in slot 0, so all our accesses need to be adjusted
            // by 1.
            field_index: field_index + 1,
          },
        ]
      }
    }
  }

  fn emit_locals(
    &mut self,
    params: &[Var],
    ret: &Type,
    body: Locals,
  ) -> (Vec<Instruction>, Vec<ValType>) {
    let mut local_tys: Vec<ValType> = vec![];
    let mut locals: HashMap<VarId, (u32, ValType)> = params
      .iter()
      .map(|var| (var, self.types.emit_val_ty(&var.ty)))
      .collect::<Vec<_>>()
      .into_iter()
      .chain(body.binds.iter().map(|(var, _)| {
        let ty = self.types.emit_val_ty(&var.ty);
        local_tys.push(ty);
        (var, ty)
      }))
      .enumerate()
      .map(|(local, (var, ty))| (var.id, (local.try_into().unwrap(), ty)))
      .collect();

    let mut inss: Vec<Instruction> = vec![];
    // We represent our closure as just its function type (without it's environment) when passing
    // it around. This allows us to pass closures that technically have different types to the same
    // argument as long as the functions line up. For example we want an argument of type `Int -> Int`
    // to accept all closures with that funciton type, regardless of their environment type.
    //
    // Once we pass the closure into it's own definition, however, we need to recover our
    // environment type. Our environment type is what allows us to access captured variables within
    // the closure definition. To recover our environment type we cast our struct from just its
    // function type back to its full type which is the function + env.
    if let Type::ClosureEnv(closure, env) = &params[0].ty {
      let closure_env_index = self.types.emit_closure_env_index(closure, env);
      let casted_env_local: u32 = (params.len() + local_tys.len()).try_into().unwrap();
      local_tys.push(closure_env_index.as_val_ty());
      inss.extend([
        Instruction::LocalGet(locals[&params[0].id].0),
        Instruction::RefCastNonNull(HeapType::Concrete(closure_env_index)),
        Instruction::LocalSet(casted_env_local),
      ]);
      // Overwrite our local for our env parameter to refer to our casted env.
      locals.insert(
        params[0].id,
        (casted_env_local, closure_env_index.as_val_ty()),
      );
    }
    for (var, defn) in body.binds {
      inss.extend(self.emit_anf(&locals, &var.ty, defn));
      inss.push(Instruction::LocalSet(locals[&var.id].0));
    }

    let body_ins: Vec<Instruction> = self.emit_anf(&locals, ret, body.body);
    inss.extend(body_ins);
    (inss, local_tys)
  }

  fn emit_definition(&mut self, definition: Definition) {
    let (inss, local_tys) =
      self.emit_locals(&definition.params, &definition.ret_ty, definition.body);

    let mut function = Function::new_with_locals_types(local_tys);
    for ins in inss {
      function.instruction(&ins);
    }
    function.instruction(&Instruction::Return);
    function.instruction(&Instruction::End);
    self.code.function(&function);
  }
}

pub fn emit_wasm(
    definitions: Vec<(DefinitionId, Definition)>
) -> Vec<u8> {
  let mut types = EmitType::default();
  let mut func = FunctionSection::new();
  let mut export = ExportSection::new();

  let functions: HashMap<DefinitionId, u32> = definitions
    .iter()
    .map(|(defn_id, defn)| {
      let func_indx = func.len();
      let type_indx = types.emit_defn_ty(defn);
      func.function(type_indx);
      export.export(&format!("func{}", defn_id.0), ExportKind::Func, func_indx);
      (*defn_id, func_indx)
    })
    .collect();

  let mut emitter = EmitWasm {
    types,
    func,
    functions,
    code: CodeSection::default(),
  };
  for (_, definition) in definitions {
    emitter.emit_definition(definition);
  }

  let mut module = Module::default();

  module
    .section(&emitter.types.into_type_section())
    .section(&emitter.func)
    .section(&export)
    .section(&emitter.code);

  module.finish()
}*/
struct EmitLocals {
  next_local: u32,
  locals: HashMap<VarId, (u32, ValType)>,
  local_tys: Vec<ValType>,
}

impl EmitLocals {
  fn param_for(&mut self, id: VarId, ty: ValType) -> u32 {
    let local = self.next_local;
    self.next_local += 1;
    self.locals.insert(id, (local, ty));
    local
  }

  fn local_for(&mut self, id: VarId, ty: ValType) -> u32 {
    let local = self.next_local;
    self.next_local += 1;
    self.local_tys.push(ty);
    self.locals.insert(id, (local, ty));
    local
  }

  fn anon_local(&mut self, ty: ValType) -> u32 {
    let local = self.next_local;
    self.next_local += 1;
    self.local_tys.push(ty);
    local
  }
}

impl Index<&VarId> for EmitLocals {
  type Output = (u32, ValType);

  fn index(&self, index: &VarId) -> &Self::Output {
    &self.locals[index]
  }
}

struct EmitWasm {
  types: EmitType,
  func: FunctionSection,
  functions: HashMap<ItemId, u32>,
  code: CodeSection,
}

impl EmitWasm {
  fn emit_item(&mut self, item: Item) {
    let (inss, local_tys) = self.emit_body(&item.params, item.body);

    let mut function = Function::new_with_locals_types(local_tys);
    for ins in inss {
      function.instruction(&ins);
    }
    function.instruction(&Instruction::Return);
    function.instruction(&Instruction::End);
    self.code.function(&function);
  }

  fn emit_body(&mut self, params: &[Var], body: IR) -> (Vec<Instruction<'static>>, Vec<ValType>) {
    let mut locals = EmitLocals {
      next_local: 0,
      locals: HashMap::default(),
      local_tys: vec![],
    };
    for param in params {
      let val_ty = self.types.emit_val_ty(&param.ty);
      locals.param_for(param.id, val_ty);
    }
    let mut inss: Vec<Instruction> = vec![];

    if let Type::ClosureEnv(closure, env) = &params[0].ty {
      let closure_env_index = self.types.emit_closure_env_index(closure, env);
      let casted_env_local = locals.anon_local(closure_env_index.as_val_ty());
      inss.extend([
        Instruction::LocalGet(locals[&params[0].id].0),
        Instruction::RefCastNonNull(HeapType::Concrete(closure_env_index)),
        Instruction::LocalSet(casted_env_local),
      ]);

      locals.locals.insert(
        params[0].id,
        (casted_env_local, closure_env_index.as_val_ty()),
      );
    }

    self.emit_ir(body, &mut locals, &mut inss);

    (inss, locals.local_tys)
  }

  fn emit_ir(&mut self, body: IR, locals: &mut EmitLocals, inss: &mut Vec<Instruction>) {
    match body {
      IR::Var(var) => {
        inss.push(Instruction::LocalGet(locals[&var.id].0));
      }
      IR::Int(i) => inss.push(Instruction::I32Const(i)),
      IR::Closure(ty, item_id, vars) => {
        let func_index = self.functions[&item_id];
        let struct_index = self
          .types
          .emit_closure_env_index(&ty, &vars.iter().map(|v| v.ty.clone()).collect::<Vec<_>>());
        let ValType::Ref(RefType { heap_type, .. }) = self.types.emit_val_ty(&ty) else {
          panic!("ICE: Closure assigned to variable with non closure type");
        };
        inss.push(Instruction::RefFunc(func_index));
        inss.extend(
          vars
            .into_iter()
            .map(|var| Instruction::LocalGet(locals[&var.id].0)),
        );
        inss.push(Instruction::StructNew(struct_index));
        inss.push(Instruction::RefCastNonNull(heap_type));
      }
      IR::Apply(fun, arg) => {
        let local_ty = fun.type_of();
        let Type::Closure(arg_ty, ret_ty) = local_ty else {
          panic!("ICE: Expected clsoure type for function of apply");
        };
        let closure_indices = self.types.emit_closure_index(&arg_ty, &ret_ty);
        self.emit_ir(*fun, locals, inss);
        let fun_local = locals.anon_local(closure_indices.struct_index.as_val_ty());
        inss.push(Instruction::LocalTee(fun_local));
        self.emit_ir(*arg, locals, inss);
        inss.extend([
          Instruction::LocalGet(fun_local),
          Instruction::StructGet {
            struct_type_index: closure_indices.struct_index,
            field_index: 0, // We know the code field is always 0
          },
          Instruction::CallRef(closure_indices.func_index),
        ]);
      }
      IR::Local(var, defn, body) => {
        self.emit_ir(*defn, locals, inss);
        let val_ty = self.types.emit_val_ty(&var.ty);
        println!("{:?} {:?}", pretty_string(var.ty, 80), val_ty);
        let local = locals.local_for(var.id, val_ty);
        inss.push(Instruction::LocalSet(local));
        self.emit_ir(*body, locals, inss);
      }
      IR::Access(strukt, field) => {
        let ty = strukt.type_of();
        let Type::ClosureEnv(closure, env) = ty else {
          panic!("ICE: Expected closure env type for struct access");
        };
        let struct_type_index = self.types.emit_closure_env_index(&closure, &env);
        self.emit_ir(*strukt, locals, inss);
        inss.push(Instruction::StructGet {
          struct_type_index,
          field_index: field.try_into().unwrap(),
        });
      }
    }
  }
}

pub fn emit_wasm(items: Vec<(ItemId, Item)>) -> Vec<u8> {
  let mut types = EmitType::default();
  let mut func = FunctionSection::new();
  let mut export = ExportSection::new();

  let functions: HashMap<ItemId, u32> = items
    .iter()
    .map(|(item_id, item)| {
      let func_index = func.len();
      let type_index = types.emit_item_ty(item);
      func.function(type_index);
      export.export(&format!("func{}", item_id.0), ExportKind::Func, func_index);
      (*item_id, func_index)
    })
    .collect();

  let mut emitter = EmitWasm {
    types,
    func,
    functions,
    code: CodeSection::default(),
  };

  for (_, item) in items {
    emitter.emit_item(item);
  }

  let mut module = Module::default();
  module
    .section(&emitter.types.into_type_section())
    .section(&emitter.func)
    .section(&export)
    .section(&emitter.code);

  module.finish()
}
#[cfg(test)]
mod tests {
  use crate::emit_wasm;

  use closure_convert_base::{closure_convert, ItemId};
  use expect_test::expect;
  use lowering_base::{self as ir, lower, IR};
  use monomorph_base::monomorph;
  use simplify_base::simplify;
  use types_base::{self as ast, builder::{make_vars, AstBuilder}, type_infer, Ast};
  use wasmparser::{Validator, WasmFeatures};
  use wasmprinter::PrintFmtWrite;
  use wasmtime::{Config, Engine, Linker, Module, Store};

  fn trivial_monomorph(ir: IR) -> IR {
    let mut types = vec![];
    let mut fun = &ir;
    // Assume all types are Int.
    // This can't be wrong for base because we don't yet support any interesting types.
    // Any function getting passed around will use a function type not a
    while let IR::TyFun(_, body) = fun {
      types.push(ir::Type::Int);
      fun = body;
    }
    monomorph(ir, types)
  }

  fn wasm_module_of(ast: Ast<ast::Var>) -> Vec<u8> {
    let (ast, scheme) = type_infer(ast).expect("Type inferce failed");
    let (ir, _) = lower(ast, scheme);
    let out = closure_convert(trivial_monomorph(simplify(ir)));

    let main_defn = ItemId(
      out
        .closure_items
        .last_key_value()
        .map(|(key, _)| key.0 + 1)
        .unwrap_or(0),
    );
    let mut defns = out.closure_items;
    defns.insert(main_defn, out.item);

    emit_wasm(defns.into_iter().collect())
  }

  #[test]
  fn test_closure_conversion() {
    let b = AstBuilder::default();
    let [add, x, y, p, q, g, h, f] = make_vars();
    let ast = b.funs(
      [add, h],
      b.locals(
        [
          (
            f,
            b.funs([q, x], b.apps(b.var(add), [b.var(q), b.var(x)])),
          ),
          (
            g,
            b.funs([p, y], b.apps(b.var(add), [b.var(p), b.var(y)])),
          ),
        ],
        b.apps(
          b.var(h),
          [
            b.app(b.var(f), b.int(3)),
            b.app(b.var(g), b.int(5)),
          ],
        ),
      ),
    );

    let module_bytes = wasm_module_of(ast);

    let mut wat = wasmprinter::PrintFmtWrite(String::new());
    let mut config = wasmprinter::Config::new();
    config
      .fold_instructions(true)
      .indent_text("  ")
      .print(&module_bytes, &mut wat)
      .expect("Printing WAT failed");
    let expect = expect![[r#"
        (module
          (type (;0;) (func (param (ref struct) i32) (result i32)))
          (type (;1;) (sub (struct (field (ref 0)))))
          (type (;2;) (func (param (ref struct) i32) (result (ref 1))))
          (type (;3;) (sub (struct (field (ref 2)))))
          (type (;4;) (func (param (ref struct) (ref 1)) (result i32)))
          (type (;5;) (sub (struct (field (ref 4)))))
          (type (;6;) (func (param (ref struct) (ref 1)) (result (ref 5))))
          (type (;7;) (sub (struct (field (ref 6)))))
          (type (;8;) (func (param (ref 3) (ref 7)) (result i32)))
          (type (;9;) (sub final 1 (struct (field (ref 0)) (field (ref 3)))))
          (export "func0" (func 0))
          (export "func1" (func 1))
          (export "func2" (func 2))
          (func (;0;) (type 0) (param (ref struct) i32) (result i32)
            (local (ref 9) (ref 3) (ref 3) (ref 1))
            (local.set 2
              (ref.cast (ref 9)
                (local.get 0)))
            (local.set 3
              (struct.get 9 1
                (local.get 2)))
            (return
              (call_ref 0
                (local.tee 5
                  (call_ref 2
                    (local.tee 4
                      (local.get 3))
                    (i32.const 3)
                    (struct.get 3 0
                      (local.get 4))))
                (local.get 1)
                (struct.get 1 0
                  (local.get 5))))
          )
          (func (;1;) (type 0) (param (ref struct) i32) (result i32)
            (local (ref 9) (ref 3) (ref 3) (ref 1))
            (local.set 2
              (ref.cast (ref 9)
                (local.get 0)))
            (local.set 3
              (struct.get 9 1
                (local.get 2)))
            (return
              (call_ref 0
                (local.tee 5
                  (call_ref 2
                    (local.tee 4
                      (local.get 3))
                    (i32.const 5)
                    (struct.get 3 0
                      (local.get 4))))
                (local.get 1)
                (struct.get 1 0
                  (local.get 5))))
          )
          (func (;2;) (type 8) (param (ref 3) (ref 7)) (result i32)
            (local (ref 7) (ref 5))
            (return
              (call_ref 4
                (local.tee 3
                  (call_ref 6
                    (local.tee 2
                      (local.get 1))
                    (ref.cast (ref 1)
                      (struct.new 9
                        (ref.func 0)
                        (local.get 0)))
                    (struct.get 7 0
                      (local.get 2))))
                (ref.cast (ref 1)
                  (struct.new 9
                    (ref.func 1)
                    (local.get 0)))
                (struct.get 5 0
                  (local.get 3))))
          )
        )
    "#]];
    expect.assert_eq(&wat.0);

    let mut validator = Validator::new_with_features(WasmFeatures::default());
    match validator.validate_all(&module_bytes) {
      Ok(_) => {}
      Err(err) => {
        let mut wat = wasmprinter::PrintFmtWrite(String::new());
        config
          .print_offsets(true)
          .print(&module_bytes, &mut wat)
          .unwrap();
        panic!("{}\n{}", &wat.0, err);
      }
    }
  }

  #[test]
  fn test_wasm_execution() {
    let b = AstBuilder::default();
    let [add, x, y, f, g, h, j] = make_vars();
    let ast = b.funs(
      [add, x, y],
      b.locals(
        [
          (
            f,
            b.fun(h, b.apps(b.var(add), [b.var(h), b.var(y)])),
          ),
          (
            g,
            b.fun(j, b.apps(b.var(add), [b.var(x), b.var(j)])),
          ),
        ],
        b.apps(
          b.var(add),
          [
            b.app(b.var(f), b.int(3)),
            b.app(b.var(g), b.int(5)),
          ],
        ),
      ),
    );

    let module_bytes = wasm_module_of(ast);

    let mut wat = wasmprinter::PrintFmtWrite(String::new());
    let mut config = wasmprinter::Config::new();
    config
      .fold_instructions(true)
      .indent_text("  ")
      .print(&module_bytes, &mut wat)
      .expect("Printing WAT failed");
    let expect = expect![[r#"
        (module
          (type (;0;) (func (param (ref struct) i32) (result i32)))
          (type (;1;) (sub (struct (field (ref 0)))))
          (type (;2;) (func (param (ref struct) i32) (result (ref 1))))
          (type (;3;) (sub (struct (field (ref 2)))))
          (type (;4;) (func (param (ref 3) i32 i32) (result i32)))
          (export "func0" (func 0))
          (func (;0;) (type 4) (param (ref 3) i32 i32) (result i32)
            (local (ref 3) (ref 3) (ref 1) (ref 1) (ref 3) (ref 1))
            (return
              (call_ref 0
                (local.tee 6
                  (call_ref 2
                    (local.tee 3
                      (local.get 0))
                    (call_ref 0
                      (local.tee 5
                        (call_ref 2
                          (local.tee 4
                            (local.get 0))
                          (i32.const 3)
                          (struct.get 3 0
                            (local.get 4))))
                      (local.get 2)
                      (struct.get 1 0
                        (local.get 5)))
                    (struct.get 3 0
                      (local.get 3))))
                (call_ref 0
                  (local.tee 8
                    (call_ref 2
                      (local.tee 7
                        (local.get 0))
                      (local.get 1)
                      (struct.get 3 0
                        (local.get 7))))
                  (i32.const 5)
                  (struct.get 1 0
                    (local.get 8)))
                (struct.get 1 0
                  (local.get 6))))
          )
        )
    "#]];
    expect.assert_eq(&wat.0);

    let mut validator = Validator::new_with_features(WasmFeatures::default());
    match validator.validate_all(&module_bytes) {
      Ok(_) => {}
      Err(err) => {
        let mut wat = wasmprinter::PrintFmtWrite(String::new());
        config
          .print_offsets(true)
          .print(&module_bytes, &mut wat)
          .unwrap();
        panic!("{}\n{}", &wat.0, err);
      }
    }

    env_logger::init();

    let (engine, mut store, mut linker) = init_wasmtime().unwrap();
    let module = Module::new(&engine, &module_bytes).unwrap();
    linker.module(&mut store, "test", &module).unwrap();

    let str = r#"
        (module
          (type $add-inner-func (;0;) (func (param (ref struct) i32) (result i32)))
          (type $add-inner-clos (;1;) (sub (struct (field (ref 0)))))
          (type $add-func (;2;) (func (param (ref struct) i32) (result (ref 1))))
          (type $add-clos (;3;) (sub (struct (field (ref 2)))))
          (type $func0-func (;4;) (func (param (ref 3) i32 i32) (result i32)))
          (type $add-inner-env (sub final $add-inner-clos (struct (field $code (ref $add-inner-func)) (field $a i32))))
          (type $main-func (func (result i32)))
          (import "test" "func0" (func $func0 (type $func0-func)))
          (export "main" (func $main))
          (export "add" (func $add))
          (export "add-inner" (func $add-inner))
          (func $add-inner (type $add-inner-func) (param $clos (ref struct)) (param $b i32) (result i32)
            (local $env (ref $add-inner-env))
            (local.set $env
             (ref.cast (ref $add-inner-env)
              (local.get $clos)))
            (i32.add
              (struct.get $add-inner-env $a (local.get $env))
              (local.get $b)))
          (func $add (type $add-func) (param $clos (ref struct)) (param $a i32) (result (ref $add-inner-clos))
            (struct.new $add-inner-env
              (ref.func $add-inner)
              (local.get $a)))
          (func $main (type $main-func) (result i32)
           (call $func0
            (struct.new $add-clos
             (ref.func $add))
            (i32.const 5)
            (i32.const 3))))
"#;
    let other_module = Module::new(&engine, str)
      .inspect_err(|_| {
        let x = wat::parse_str(str).unwrap();
        let mut s = PrintFmtWrite(String::new());
        wasmprinter::Config::new()
          .fold_instructions(false)
          .print_offsets(true)
          .indent_text("  ")
          .print(&x, &mut s)
          .unwrap();
        println!("{}", s.0);
      })
      .unwrap();

    let inst = linker.instantiate(&mut store, &other_module).unwrap();
    let main = inst
      .get_typed_func::<(), (i32,)>(&mut store, "main")
      .unwrap();
    let (res,) = main.call(&mut store, ()).unwrap();
    assert_eq!(res, 16);
  }

  fn init_wasmtime() -> Result<(Engine, Store<()>, Linker<()>), wasmtime::Error> {
    let mut config = Config::new();
    config
      .wasm_gc(true)
      .wasm_function_references(true)
      .wasm_bulk_memory(true)
      .wasm_tail_call(true);
    let engine = Engine::new(&config)?;
    let store = Store::new(&engine, ());
    let linker = Linker::new(&engine);
    Ok((engine, store, linker))
  }
}
