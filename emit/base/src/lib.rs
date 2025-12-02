use std::collections::HashMap;
use std::ops::Index;

use closure_convert_base::{Item, ItemId, Type, Var, VarId, IR};
use wasm_encoder::{
  AbstractHeapType, CodeSection, CompositeInnerType, CompositeType, ExportKind, ExportSection,
  FieldType, FuncType, Function, FunctionSection, HeapType, Instruction, Module, RefType,
  StorageType, StructType, SubType, TypeSection, ValType,
};

#[derive(Eq, Hash, PartialEq)]
enum PartialTy {
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
  types: Vec<PartialTy>,
  supertypes: HashMap<u32, u32>,
}

impl EmitType {
  fn into_type_section(self) -> TypeSection {
    let mut sect = TypeSection::new();
    for (i, ty) in self.types.into_iter().enumerate() {
      let (inner, is_final) = match ty {
        PartialTy::Func(func_type) => (CompositeInnerType::Func(func_type), true),
        PartialTy::Struct(fields, is_final) => (
          CompositeInnerType::Struct(StructType {
            fields: fields.into_boxed_slice(),
          }),
          is_final,
        ),
      };
      let indx: u32 = i.try_into().unwrap();
      let supertype_idx = self.supertypes.get(&indx).copied();
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

  fn emit_ref_ty(&mut self, key: PartialTy) -> u32 {
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

    let func_index = self.emit_ref_ty(PartialTy::Func(FuncType::new(
      [abstract_struct_ty(), arg_valty],
      [ret_valty],
    )));
    let struct_index = self.emit_ref_ty(PartialTy::Struct(
      vec![FieldType {
        element_type: StorageType::Val(func_index.as_val_ty()),
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
    let fields = std::iter::once(code_field)
      .chain(env.iter().map(|ty| FieldType {
        element_type: StorageType::Val(self.emit_val_ty(ty)),
        mutable: false,
      }))
      .collect();

    let abstract_indx = self.emit_ref_ty(PartialTy::Struct(vec![code_field], false));
    let concrete_indx = self.emit_ref_ty(PartialTy::Struct(fields, true));
    self.supertypes.insert(concrete_indx, abstract_indx);
    concrete_indx
  }

  fn emit_val_ty(&mut self, ty: &Type) -> ValType {
    match ty {
      Type::Int => ValType::I32,
      Type::Closure(arg, ret) => self.emit_closure_index(arg, ret).struct_index.as_val_ty(),
      Type::ClosureEnv(closure, _) => self.emit_val_ty(closure),
    }
  }

  fn emit_item_ty(&mut self, item: &Item) -> u32 {
    let ret_ty = self.emit_val_ty(&item.ret_ty);
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
    self.emit_ref_ty(PartialTy::Func(func_ty))
  }
}

struct EmitLocals {
  next_local: u32,
  local_tys: Vec<ValType>,
  locals: HashMap<VarId, u32>,
}

impl EmitLocals {
  fn param_for(&mut self, id: VarId) -> u32 {
    let local = self.next_local;
    self.next_local += 1;
    self.locals.insert(id, local);
    local
  }

  fn local_for(&mut self, id: VarId, ty: ValType) -> u32 {
    let local = self.next_local;
    self.next_local += 1;
    self.local_tys.push(ty);
    self.locals.insert(id, local);
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
  type Output = u32;

  fn index(&self, index: &VarId) -> &Self::Output {
    &self.locals[index]
  }
}

struct EmitWasm {
  types: EmitType,
  functions: HashMap<ItemId, u32>,
}

impl EmitWasm {
  fn emit_item(&mut self, item: Item) -> Function {
    let (inss, local_tys) = self.emit_body(&item.params, item.body);

    let mut function = Function::new_with_locals_types(local_tys);
    for ins in inss {
      function.instruction(&ins);
    }
    function.instruction(&Instruction::Return);
    function.instruction(&Instruction::End);
    function
  }

  fn emit_body(&mut self, params: &[Var], body: IR) -> (Vec<Instruction<'static>>, Vec<ValType>) {
    let mut locals = EmitLocals {
      next_local: 0,
      local_tys: vec![],
      locals: HashMap::default(),
    };
    for param in params {
      locals.param_for(param.id);
    }
    let mut inss: Vec<Instruction> = vec![];

    if let Type::ClosureEnv(closure, env) = &params[0].ty {
      let closure_env_index = self.types.emit_closure_env_index(closure, env);
      let casted_env_local = locals.anon_local(closure_env_index.as_val_ty());
      inss.extend([
        Instruction::LocalGet(locals[&params[0].id]),
        Instruction::RefCastNonNull(HeapType::Concrete(closure_env_index)),
        Instruction::LocalSet(casted_env_local),
      ]);

      locals.locals.insert(params[0].id, casted_env_local);
    }

    self.emit_ir(body, &mut locals, &mut inss);

    (inss, locals.local_tys)
  }

  fn emit_ir(&mut self, body: IR, locals: &mut EmitLocals, inss: &mut Vec<Instruction>) {
    match body {
      IR::Var(var) => {
        inss.push(Instruction::LocalGet(locals[&var.id]));
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
            .map(|var| Instruction::LocalGet(locals[&var.id])),
        );
        inss.push(Instruction::StructNew(struct_index));
        inss.push(Instruction::RefCastNonNull(heap_type));
      }
      IR::Apply(fun, arg) => {
        let local_ty = fun.type_of();
        let Type::Closure(arg_ty, ret_ty) = local_ty else {
          panic!("ICE: Expected closure type for function of apply");
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

  let mut emitter = EmitWasm { types, functions };
  let mut code = CodeSection::default();
  for (_, item) in items {
    code.function(&emitter.emit_item(item));
  }

  let mut module = Module::default();
  module
    .section(&emitter.types.into_type_section())
    .section(&func)
    .section(&export)
    .section(&code);

  module.finish()
}

#[cfg(test)]
mod tests {
  use crate::emit_wasm;

  use closure_convert_base::{closure_convert, ItemId};
  use expect_test::expect;
  use lowering_base::lower;
  use monomorph_base::trivial_monomorph;
  use simplify_base::simplify;
  use types_base::{
    self as ast,
    builder::{make_vars, AstBuilder},
    type_infer, Ast,
  };
  use wasmparser::{Validator, WasmFeatures};
  use wasmprinter::PrintFmtWrite;
  use wasmtime::{Config, Engine, Linker, Module, Store};

  fn wasm_module_of(ast: Ast<ast::Var>) -> Vec<u8> {
    let out = type_infer(ast);
    let (ir, _) = lower(out.ast, out.scheme);
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
          (f, b.funs([q, x], b.apps(b.var(add), [b.var(q), b.var(x)]))),
          (g, b.funs([p, y], b.apps(b.var(add), [b.var(p), b.var(y)]))),
        ],
        b.apps(
          b.var(h),
          [b.app(b.var(f), b.int(3)), b.app(b.var(g), b.int(5))],
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
          (f, b.fun(h, b.apps(b.var(add), [b.var(h), b.var(y)]))),
          (g, b.fun(j, b.apps(b.var(add), [b.var(x), b.var(j)]))),
        ],
        b.apps(
          b.var(add),
          [b.app(b.var(f), b.int(3)), b.app(b.var(g), b.int(5))],
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

    let _ = env_logger::try_init();

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

  #[test]
  fn test_return_closures() {
    let b = AstBuilder::default();
    let [add, f, x, y, z, a] = make_vars();
    let ast = b.fun(
      add,
      b.locals(
        [
          (
            f,
            b.fun(
              x,
              b.locals(
                [(z, b.apps(b.var(add), [b.var(x), b.int(1)]))],
                b.fun(y, b.apps(b.var(add), [b.var(z), b.var(y)])),
              ),
            ),
          ),
          (a, b.app(b.var(f), b.int(2))),
        ],
        b.apps(
          b.var(add),
          [
            b.apps(b.var(f), [b.int(3), b.int(4)]),
            b.apps(b.var(a), [b.int(2)]),
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
          (type (;4;) (func (param (ref 3)) (result i32)))
          (type (;5;) (sub final 1 (struct (field (ref 0)) (field (ref 3)) (field i32))))
          (type (;6;) (sub final 3 (struct (field (ref 2)) (field (ref 3)))))
          (export "func0" (func 0))
          (export "func1" (func 1))
          (export "func2" (func 2))
          (func (;0;) (type 0) (param (ref struct) i32) (result i32)
            (local (ref 5) i32 (ref 3) (ref 3) (ref 1))
            (local.set 2
              (ref.cast (ref 5)
                (local.get 0)))
            (local.set 3
              (struct.get 5 2
                (local.get 2)))
            (local.set 4
              (struct.get 5 1
                (local.get 2)))
            (return
              (call_ref 0
                (local.tee 6
                  (call_ref 2
                    (local.tee 5
                      (local.get 4))
                    (local.get 3)
                    (struct.get 3 0
                      (local.get 5))))
                (local.get 1)
                (struct.get 1 0
                  (local.get 6))))
          )
          (func (;1;) (type 2) (param (ref struct) i32) (result (ref 1))
            (local (ref 6) (ref 3) (ref 3) (ref 1) i32)
            (local.set 2
              (ref.cast (ref 6)
                (local.get 0)))
            (local.set 3
              (struct.get 6 1
                (local.get 2)))
            (local.set 6
              (call_ref 0
                (local.tee 5
                  (call_ref 2
                    (local.tee 4
                      (local.get 3))
                    (local.get 1)
                    (struct.get 3 0
                      (local.get 4))))
                (i32.const 1)
                (struct.get 1 0
                  (local.get 5))))
            (return
              (ref.cast (ref 1)
                (struct.new 5
                  (ref.func 0)
                  (local.get 3)
                  (local.get 6))))
          )
          (func (;2;) (type 4) (param (ref 3)) (result i32)
            (local (ref 3) (ref 3) (ref 3) (ref 1) (ref 1) (ref 3) (ref 1))
            (local.set 1
              (ref.cast (ref 3)
                (struct.new 6
                  (ref.func 1)
                  (local.get 0))))
            (return
              (call_ref 0
                (local.tee 5
                  (call_ref 2
                    (local.tee 2
                      (local.get 0))
                    (call_ref 0
                      (local.tee 4
                        (call_ref 2
                          (local.tee 3
                            (local.get 1))
                          (i32.const 3)
                          (struct.get 3 0
                            (local.get 3))))
                      (i32.const 4)
                      (struct.get 1 0
                        (local.get 4)))
                    (struct.get 3 0
                      (local.get 2))))
                (call_ref 0
                  (local.tee 7
                    (call_ref 2
                      (local.tee 6
                        (local.get 1))
                      (i32.const 2)
                      (struct.get 3 0
                        (local.get 6))))
                  (i32.const 2)
                  (struct.get 1 0
                    (local.get 7)))
                (struct.get 1 0
                  (local.get 5))))
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

    let _ = env_logger::try_init();

    let (engine, mut store, mut linker) = init_wasmtime().unwrap();
    let module = Module::new(&engine, &module_bytes).unwrap();
    linker.module(&mut store, "test", &module).unwrap();

    let str = r#"
        (module
          (type $add-inner-func (;0;) (func (param (ref struct) i32) (result i32)))
          (type $add-inner-clos (;1;) (sub (struct (field (ref 0)))))
          (type $add-func (;2;) (func (param (ref struct) i32) (result (ref 1))))
          (type $add-clos (;3;) (sub (struct (field (ref 2)))))
          (type $func0-func (;4;) (func (param (ref 3)) (result i32)))
          (type $add-inner-env (sub final $add-inner-clos (struct (field $code (ref $add-inner-func)) (field $a i32))))
          (type $main-func (func (result i32)))
          (import "test" "func2" (func $func0 (type $func0-func)))
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
             (ref.func $add)))))
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
    assert_eq!(res, 13);
  }

  #[test]
  fn test_example() {
    let b = AstBuilder::default();
    let [add, f] = make_vars();
    let ast = b.fun(
      add,
      b.locals(
        [(f, b.apps(b.var(add), [b.int(1)]))],
        b.apps(
          b.var(add),
          [
            b.apps(b.var(f), [b.int(400)]),
            b.apps(b.var(f), [b.int(1234)]),
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
          (type (;4;) (func (param (ref 3)) (result i32)))
          (export "func0" (func 0))
          (func (;0;) (type 4) (param (ref 3)) (result i32)
            (local (ref 3) (ref 1) (ref 3) (ref 1) (ref 1) (ref 1))
            (local.set 2
              (call_ref 2
                (local.tee 1
                  (local.get 0))
                (i32.const 1)
                (struct.get 3 0
                  (local.get 1))))
            (return
              (call_ref 0
                (local.tee 5
                  (call_ref 2
                    (local.tee 3
                      (local.get 0))
                    (call_ref 0
                      (local.tee 4
                        (local.get 2))
                      (i32.const 400)
                      (struct.get 1 0
                        (local.get 4)))
                    (struct.get 3 0
                      (local.get 3))))
                (call_ref 0
                  (local.tee 6
                    (local.get 2))
                  (i32.const 1234)
                  (struct.get 1 0
                    (local.get 6)))
                (struct.get 1 0
                  (local.get 5))))
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

    let _ = env_logger::try_init();

    let (engine, mut store, mut linker) = init_wasmtime().unwrap();
    let module = Module::new(&engine, &module_bytes).unwrap();
    linker.module(&mut store, "test", &module).unwrap();

    let str = r#"
        (module
          (type $add-inner-func (;0;) (func (param (ref struct) i32) (result i32)))
          (type $add-inner-clos (;1;) (sub (struct (field (ref 0)))))
          (type $add-func (;2;) (func (param (ref struct) i32) (result (ref 1))))
          (type $add-clos (;3;) (sub (struct (field (ref 2)))))
          (type $func0-func (;4;) (func (param (ref 3)) (result i32)))
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
             (ref.func $add)))))
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
    assert_eq!(res, 1636);
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
