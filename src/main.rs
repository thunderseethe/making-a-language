#![allow(dead_code)]
use std::collections::{BTreeSet, HashMap, HashSet};

use ena::unify::InPlaceUnificationTable;

use crate::ty::ClosedRow;

use self::ast::{Ast, Operation, TypedVar, Var};
use self::infer::TypeAndEff;
use self::subst::SubstOut;
use self::ty::{
  Data, DataRowCombination, Eff, EffRowCombination, Row, RowCombination, RowVar, Type, TypeVar,
};
use self::unification::TypeError;

mod ast;
mod infer;
mod subst;
mod ty;
mod unification;

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
pub enum Constraint {
  TypeEqual(Type, Type),
  DataEqual(Row, Row),
  DataCombo(DataRowCombination),
  EffEqual(Row, Row),
  EffCombo(EffRowCombination),
  Handles {
    handler: Row,
    eff: Row,
    ret: Type,
  },
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
pub struct TypeInference {
  unification_table: InPlaceUnificationTable<TypeVar>,
  row_unification_table: InPlaceUnificationTable<RowVar>,
  partial_data_row_combs: BTreeSet<RowCombination<Data>>,
  partial_eff_row_combs: BTreeSet<RowCombination<Eff>>,
  // In a real compile we would have parse and name resolved all our in scope effect definitions.
  // We can imagine the result of that would produce something like effect source that provides
  // metadata about our effects.
  effect_source: EffectSource,
}

impl TypeInference {
  pub fn new(effect_source: EffectSource) -> Self {
    Self {
      unification_table: InPlaceUnificationTable::default(),
      row_unification_table: InPlaceUnificationTable::default(),
      partial_data_row_combs: BTreeSet::default(),
      partial_eff_row_combs: BTreeSet::default(),
      effect_source,
    }
  }
}

pub struct EffectDefn {
  name: String,
  ops: HashMap<Operation, EffectOpDefn>,
}
pub struct EffectOpDefn {
  name: String,
  ty: Type,
}
pub struct EffectSource {
  effects: Vec<EffectDefn>,
  effects_by_op: HashMap<Operation, usize>,
}
impl EffectSource {
  fn new(effects: Vec<EffectDefn>) -> Self {
    let mut effects_by_op = HashMap::new();
    for (indx, effect) in effects.iter().enumerate() {
      for op in effect.ops.keys() {
        effects_by_op.insert(*op, indx);
      }
    }
    Self {
      effects,
      effects_by_op,
    }
  }

  fn effect_op_defn<'a>(&'a self, op_name: &Operation) -> &'a EffectOpDefn {
    let eff_indx = self.effects_by_op[op_name];
    let eff_defn = &self.effects[eff_indx];
    &eff_defn.ops[op_name]
  }
  fn effect_member_sig(&self, op_name: &Operation) -> Type {
    self.effect_op_defn(op_name).ty.clone()
  }
  fn effect_name_str_of_op(&self, op_name: &Operation) -> String {
    let eff_indx = self.effects_by_op[op_name];
    let eff_defn = &self.effects[eff_indx];
    eff_defn.name.clone()
  }

  fn effect_handler_signature(&self, eff_name: String) -> EffectHandlerSig {
    let eff_defn = self
      .effects
      .iter()
      .find(|defn| defn.name == eff_name)
      .unwrap();
    // Because this will be a TypeScheme, we're allowed to cheat here and use 0 as our type
    // variable. Instantiation will always turn this into a different variable before it gets
    // unified anywhere, so it won't conflict with other 0 variables.
    let ret_tyvar = TypeVar(0);
    let ret = Type::Var(ret_tyvar);
    let handler_ty = Type::Prod(Row::Closed(ClosedRow::from(
      eff_defn
        .ops
        .values()
        .map(|op_defn| {
          (
            op_defn.name.clone(),
            match op_defn.ty.clone() {
              Type::Fun(a, b) => Type::fun(*a, Type::fun(Type::fun(*b, ret.clone()), ret.clone())),
              _ => unreachable!("Effect operations must be function types"),
            },
          )
        })
        .collect::<Vec<_>>(),
    )));
    EffectHandlerSig {
      ret_ty: ret_tyvar,
      sig: TypeScheme::with_ty(handler_ty),
    }
  }

  fn lookup_effect_by_handler(&self, handler_fields: &[String]) -> Option<String> {
    self.effects.iter().find_map(|eff_defn| {
      let mut eff_fields = eff_defn
        .ops
        .values()
        .map(|op_defn| op_defn.name.clone())
        .collect::<Vec<_>>();
      // If we wanted to do this fast we wouldn't store our operations in a hashmap, then we
      // could keep them ordered lexographically and we wouldn't have to sort them everytime.
      eff_fields.sort();
      (handler_fields == eff_fields).then_some(eff_defn.name.clone())
    })
  }
}

impl TypeInference {
  fn effect_member_sig(&self, op_name: Operation) -> Type {
    self.effect_source.effect_member_sig(&op_name)
  }

  fn effect_name_str_of_op(&self, op_name: Operation) -> String {
    self.effect_source.effect_name_str_of_op(&op_name)
  }

  fn effect_handler_signature(&self, eff_name: String) -> EffectHandlerSig {
    self.effect_source.effect_handler_signature(eff_name)
  }

  fn lookup_effect_by_handler(&self, handler_fields: &[String]) -> Option<String> {
    self.effect_source.lookup_effect_by_handler(handler_fields)
  }

  fn instantiate(
    &mut self,
    sig: TypeScheme,
  ) -> (Type, HashMap<TypeVar, TypeVar>, HashMap<RowVar, RowVar>) {
    fn fold_row(tys: &HashMap<TypeVar, TypeVar>, rows: &HashMap<RowVar, RowVar>, row: Row) -> Row {
      match row {
        Row::Open(var) => Row::Open(rows[&var]),
        Row::Closed(row) => Row::Closed(ClosedRow {
          fields: row.fields,
          values: row
            .values
            .into_iter()
            .map(|ty| fold_ty(tys, rows, ty))
            .collect(),
        }),
      }
    }
    fn fold_ty(tys: &HashMap<TypeVar, TypeVar>, rows: &HashMap<RowVar, RowVar>, ty: Type) -> Type {
      match ty {
        Type::Int => Type::Int,
        Type::Var(var) => Type::Var(tys[&var]),
        Type::Fun(arg, ret) => Type::fun(fold_ty(tys, rows, *arg), fold_ty(tys, rows, *ret)),
        Type::Prod(row) => Type::Prod(fold_row(tys, rows, row)),
        Type::Sum(row) => Type::Sum(fold_row(tys, rows, row)),
        Type::Label(lbl, ty) => Type::label(lbl, fold_ty(tys, rows, *ty)),
      }
    }

    let inst_ty = sig
      .unbound_tys
      .into_iter()
      .map(|ty| (ty, self.fresh_ty_var()))
      .collect::<HashMap<_, _>>();
    let inst_row = sig
      .unbound_rows
      .into_iter()
      .map(|row| (row, self.fresh_row_var()))
      .collect::<HashMap<_, _>>();
    let ty = fold_ty(&inst_ty, &inst_row, sig.ty);
    (ty, inst_ty, inst_row)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Evidence {
  DataEquation { left: Row, right: Row, goal: Row },
  EffEquation { left: Row, right: Row, goal: Row },
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct TypeScheme {
  unbound_rows: HashSet<RowVar>,
  unbound_tys: HashSet<TypeVar>,
  evidence: Vec<Evidence>,
  eff: Row,
  ty: Type,
}
impl TypeScheme {
  fn with_ty(ty: Type) -> Self {
    Self {
      ty,
      eff: Row::Closed(ClosedRow {
        fields: vec![],
        values: vec![],
      }),
      unbound_tys: HashSet::default(),
      unbound_rows: HashSet::default(),
      evidence: vec![],
    }
  }
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct EffectHandlerSig {
  ret_ty: TypeVar,
  sig: TypeScheme,
}
impl EffectHandlerSig {
  fn into_scheme(mut self) -> TypeScheme {
    self.sig.unbound_tys.insert(self.ret_ty);
    self.sig
  }
}

static STATE_GET: Operation = Operation(0);
static STATE_PUT: Operation = Operation(1);
static READER_ASK: Operation = Operation(2);

fn type_infer(ast: Ast<Var>) -> Result<(Ast<TypedVar>, TypeScheme), TypeError> {
  let mut ctx = TypeInference::new(EffectSource::new(vec![
    EffectDefn {
      name: "State".to_string(),
      ops: vec![
        (
          STATE_GET,
          EffectOpDefn {
            name: "get".to_string(),
            ty: Type::fun(Type::unit(), Type::Int),
          },
        ),
        (
          STATE_PUT,
          EffectOpDefn {
            name: "put".to_string(),
            ty: Type::fun(Type::Int, Type::unit()),
          },
        ),
      ]
      .into_iter()
      .collect(),
    },
    EffectDefn {
      name: "Reader".to_string(),
      ops: vec![(
        READER_ASK,
        EffectOpDefn {
          name: "ask".to_string(),
          ty: Type::fun(Type::unit(), Type::Int),
        },
      )]
      .into_iter()
      .collect(),
    },
  ]));

  // Constraint generation
  let (out, tyeff) = ctx.infer(im::HashMap::default(), ast);

  // Constraint solving
  ctx.unification(out.constraints)?;

  // Apply our substition to our inferred types
  let subst_out = ctx
    .substitute_ty(tyeff.ty)
    .merge(ctx.substitute_row::<Eff>(tyeff.eff), TypeAndEff::new)
    .merge(ctx.substitute_ast(out.typed_ast), |tyeff, ast| (tyeff, ast));

  let mut ev_out = SubstOut::new(());
  ev_out.unbound_rows = subst_out.unbound_rows.clone();
  ev_out.unbound_tys = subst_out.unbound_tys.clone();
  let mut evidence = std::mem::take(&mut ctx.partial_data_row_combs)
    .into_iter()
    .filter_map(|row_combo| {
      let norm_combo = ctx.substitute_data_row_comb(row_combo);
      ctx_mentions_evidence(&ev_out, norm_combo.value).map(|combo| {
        ev_out.unbound_rows.extend(norm_combo.unbound_rows);
        ev_out.unbound_tys.extend(norm_combo.unbound_tys);
        combo
      })
    })
    .collect::<Vec<_>>();

  evidence.extend(
    std::mem::take(&mut ctx.partial_eff_row_combs)
      .into_iter()
      .map(|row_combo| {
        let out = ctx.substitute_eff_row_comb(row_combo);
        ev_out.unbound_tys.extend(out.unbound_tys);
        ev_out.unbound_rows.extend(out.unbound_rows);
        out.value
      }),
  );

  let subst_out = subst_out.merge(ev_out, |l, _| l);
  // Return our typed ast and it's type scheme
  Ok((
    subst_out.value.1,
    TypeScheme {
      unbound_rows: subst_out.unbound_rows,
      unbound_tys: subst_out.unbound_tys,
      evidence,
      eff: subst_out.value.0.eff,
      ty: subst_out.value.0.ty,
    },
  ))
}

fn ctx_mentions_evidence<T>(ctx: &SubstOut<T>, evidence: Evidence) -> Option<Evidence> {
  let (left, right, goal) = match &evidence {
    Evidence::DataEquation { left, right, goal } => (left, right, goal),
    Evidence::EffEquation { left, right, goal } => (left, right, goal),
  };
  fn mentions<T>(ctx: &SubstOut<T>, row: &Row) -> bool {
    match row {
      Row::Open(var) => ctx.unbound_rows.contains(var),
      Row::Closed(row) => row.mentions(&ctx.unbound_tys, &ctx.unbound_rows),
    }
  }
  (mentions(ctx, left) || mentions(ctx, right) || mentions(ctx, goal)).then_some(evidence)
}

fn main() {
  println!("Hello, world!");
}

#[cfg(test)]
mod tests {
  use crate::ast::Direction;
  use crate::ty::ClosedRow;

  use super::*;

  macro_rules! set {
        () => {{ HashSet::new() }};
        ($($ele:expr),*) => {{
            let mut tmp = HashSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

  #[test]
  fn infers_int() {
    let ast = Ast::Int(3);

    let ty_chk = type_infer(ast).expect("Type inference to succeed");
    assert_eq!(ty_chk.0, Ast::Int(3));
    assert_eq!(ty_chk.1.ty, Type::Int);
  }

  #[test]
  fn infers_id_fun() {
    let x = Var(0);
    let ast = Ast::fun(x, Ast::Var(x));

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let a = TypeVar(0);
    let eff = RowVar(0);
    let typed_x = TypedVar(x, Type::Var(a));
    assert_eq!(ty_chk.0, Ast::fun(typed_x.clone(), Ast::Var(typed_x)));
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![eff],
        unbound_tys: set![a],
        evidence: vec![],
        eff: Row::Open(eff),
        ty: Type::fun(Type::Var(a), Type::Var(a)),
      }
    )
  }

  #[test]
  fn infers_k_combinator() {
    let x = Var(0);
    let y = Var(1);
    let ast = Ast::fun(x, Ast::fun(y, Ast::Var(x)));

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let eff = RowVar(0);
    let a = TypeVar(0);
    let b = TypeVar(1);
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![eff],
        unbound_tys: set![a, b],
        evidence: vec![],
        eff: Row::Open(eff),
        ty: Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(a))),
      }
    );
  }

  #[test]
  fn infers_s_combinator() {
    let x = Var(0);
    let y = Var(1);
    let z = Var(2);
    let ast = Ast::fun(
      x,
      Ast::fun(
        y,
        Ast::fun(
          z,
          Ast::app(
            Ast::app(Ast::Var(x), Ast::Var(z)),
            Ast::app(Ast::Var(y), Ast::Var(z)),
          ),
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let eff = RowVar(3);
    let a = TypeVar(2);
    let b = TypeVar(3);
    let c = TypeVar(4);
    let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
    let y_ty = Type::fun(Type::Var(a), Type::Var(b));
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![eff],
        unbound_tys: set![a, b, c],
        evidence: vec![],
        eff: Row::Open(eff),
        ty: Type::fun(x_ty, Type::fun(y_ty, Type::fun(Type::Var(a), Type::Var(c)))),
      }
    )
  }

  fn single_row(field: impl ToString, value: Type) -> ClosedRow {
    ClosedRow {
      fields: vec![field.to_string()],
      values: vec![value],
    }
  }

  #[test]
  fn test_wand_combinator() {
    let m = Var(0);
    let n = Var(1);

    let ast = Ast::fun(
      m,
      Ast::fun(
        n,
        Ast::unlabel(
          Ast::project(Direction::Left, Ast::concat(Ast::Var(m), Ast::Var(n))),
          "x",
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let eff = RowVar(5);
    let m = RowVar(3);
    let n = RowVar(4);
    let goal = RowVar(1);
    let a = TypeVar(2);
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![n, RowVar(2), m, goal, eff],
        unbound_tys: set![a],
        evidence: vec![
          Evidence::DataEquation {
            left: Row::Open(m),
            right: Row::Open(n),
            goal: Row::Open(goal)
          },
          Evidence::DataEquation {
            left: Row::Closed(single_row("x", Type::Var(a))),
            right: Row::Open(RowVar(2)),
            goal: Row::Open(goal)
          }
        ],
        eff: Row::Open(eff),
        ty: Type::fun(
          Type::Prod(Row::Open(m)),
          Type::fun(Type::Prod(Row::Open(n)), Type::Var(a))
        )
      }
    );
  }

  #[test]
  fn test_sums() {
    let f = Var(0);
    let g = Var(1);
    let x = Var(2);
    let ast = Ast::fun(
      f,
      Ast::fun(
        g,
        Ast::fun(
          x,
          Ast::app(
            Ast::branch(Ast::Var(f), Ast::Var(g)),
            Ast::inject(Direction::Right, Ast::label("Con", Ast::Var(x))),
          ),
        ),
      ),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let eff = RowVar(4);
    let f = RowVar(5);
    let g = RowVar(6);
    let goal = RowVar(2);
    let a = TypeVar(2);
    let r = TypeVar(3);
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![g, f, RowVar(0), goal, eff],
        unbound_tys: set![a, r],
        evidence: vec![
          Evidence::DataEquation {
            left: Row::Open(RowVar(0)),
            right: Row::Closed(single_row("Con", Type::Var(a))),
            goal: Row::Open(goal)
          },
          Evidence::DataEquation {
            left: Row::Open(f),
            right: Row::Open(g),
            goal: Row::Open(goal)
          }
        ],
        eff: Row::Open(eff),
        ty: Type::fun(
          Type::fun(Type::Sum(Row::Open(f)), Type::Var(r)),
          Type::fun(
            Type::fun(Type::Sum(Row::Open(g)), Type::Var(r)),
            Type::fun(Type::Var(a), Type::Var(r))
          )
        ),
      }
    );
  }

  #[test]
  fn type_handled_reader_effect() {
    let e = Var(0);
    let k = Var(1);
    let x = Var(2);
    let ast = Ast::handle(
      Ast::concat(
        Ast::label(
          "ask",
          Ast::fun(e, Ast::fun(k, Ast::app(Ast::Var(k), Ast::Int(5)))),
        ),
        Ast::label("return", Ast::fun(x, Ast::Var(x))),
      ),
      Ast::app(Ast::Operation(READER_ASK), Ast::Unit),
    );

    let ty_chk = type_infer(ast).expect("Type inference to succeed");

    let unused = RowVar(3);
    let eff = RowVar(9);
    assert_eq!(
      ty_chk.1,
      TypeScheme {
        unbound_rows: set![eff, unused],
        unbound_tys: set![],
        evidence: vec![Evidence::EffEquation {
          left: Row::Open(eff),
          right: Row::Closed(single_row("Reader", Type::Int)),
          goal: Row::Open(unused),
        }],
        eff: Row::Open(eff),
        ty: Type::Int,
      }
    );
  }

  #[test]
  fn type_unhandled_effect() {
    let x = Var(0);
    let ast = Ast::fun(x, Ast::app(Ast::Operation(STATE_GET), Ast::Var(x)));

    let ty_chk_res = type_infer(ast).expect("Type inference to succeed");

    let unused = RowVar(1);
    let eff = RowVar(2);
    let state_ret_ty = TypeVar(2);
    assert_eq!(
      ty_chk_res.1,
      TypeScheme {
        unbound_rows: set![unused, eff],
        unbound_tys: set![state_ret_ty],
        evidence: vec![Evidence::EffEquation {
          left: Row::Open(unused),
          right: Row::Closed(single_row("State", Type::Var(state_ret_ty))),
          goal: Row::Open(eff)
        }],
        eff: Row::Open(eff),
        ty: Type::fun(Type::unit(), Type::Int),
      }
    );
  }

  #[test]
  fn type_unhandled_multi_effect() {
    let ast: Ast<Var> = Ast::app(
      Ast::Operation(STATE_PUT),
      Ast::app(Ast::Operation(READER_ASK), Ast::Unit),
    );

    let ty_chk_res = type_infer(ast).expect("Type inference to succeed");

    let unused_reader = RowVar(1);
    let unused_state = RowVar(3);
    let eff = RowVar(2);
    let reader_ret_ty = TypeVar(1);
    let state_ret_ty = TypeVar(3);
    assert_eq!(
      ty_chk_res.1,
      TypeScheme {
        unbound_rows: set![unused_reader, unused_state, eff],
        unbound_tys: set![reader_ret_ty, state_ret_ty],
        evidence: vec![
          Evidence::EffEquation {
            left: Row::Open(unused_reader),
            right: Row::Closed(single_row("Reader", Type::Var(reader_ret_ty))),
            goal: Row::Open(eff)
          },
          Evidence::EffEquation {
            left: Row::Open(unused_state),
            right: Row::Closed(single_row("State", Type::Var(state_ret_ty))),
            goal: Row::Open(eff),
          }
        ],
        eff: Row::Open(eff),
        ty: Type::unit(),
      }
    );
  }

  #[test]
  fn handle_part_of_effect_row() {
    let e = Var(0);
    let k = Var(1);
    let x = Var(2);
    let ast = Ast::handle(
      Ast::concat(
        Ast::label(
          "ask",
          Ast::fun(e, Ast::fun(k, Ast::app(Ast::Var(k), Ast::Int(34)))),
        ),
        Ast::label("return", Ast::fun(x, Ast::Var(x))),
      ),
      Ast::app(
        Ast::Operation(STATE_PUT),
        Ast::app(Ast::Operation(READER_ASK), Ast::Unit),
      ),
    );

    let ty_chk_res = type_infer(ast).expect("Type inference to succeed");

    let inner_eff = RowVar(3);
    let outer_eff = RowVar(11);
    let unused_state = RowVar(4);
    let state_ret_ty = TypeVar(4);
    // TypeScheme { unbound_rows: {RowVar(11), RowVar(3), RowVar(4)}, unbound_tys: {TypeVar(4)}, evidence: [
    //      EffEquation { left: Open(RowVar(11)), right: Closed(ClosedRow { fields: ["Reader"], values: [Prod(Closed(ClosedRow { fields: [], values: [] }))] }), goal: Open(RowVar(3)) }, 
    //      EffEquation { left: Open(RowVar(4)), right: Closed(ClosedRow { fields: ["State"], values: [Var(TypeVar(4))] }), goal: Open(RowVar(3)) }
    //  ], eff: Open(RowVar(11)), ty: Prod(Closed(ClosedRow { fields: [], values: [] })) }
    assert_eq!(
      ty_chk_res.1,
      TypeScheme {
        unbound_rows: set![inner_eff, outer_eff, unused_state],
        unbound_tys: set![state_ret_ty],
        evidence: vec![
          Evidence::EffEquation {
            left: Row::Open(outer_eff),
            right: Row::Closed(single_row("Reader", Type::unit())),
            goal: Row::Open(inner_eff)
          },
          Evidence::EffEquation {
            left: Row::Open(unused_state),
            right: Row::Closed(single_row("State", Type::Var(state_ret_ty))),
            goal: Row::Open(inner_eff),
          }
        ],
        eff: Row::Open(outer_eff),
        ty: Type::unit(),
      }
    );
  }

  #[test]
  fn type_infer_fails() {
    let x = Var(0);
    let ast = Ast::app(Ast::fun(x, Ast::app(Ast::Var(x), Ast::Int(3))), Ast::Int(1));

    let ty_chk_res = type_infer(ast);

    assert_eq!(
      ty_chk_res,
      Err(TypeError::TypeNotEqual((
        Type::fun(Type::Int, Type::Var(TypeVar(1))),
        Type::Int
      )))
    );
  }
}
