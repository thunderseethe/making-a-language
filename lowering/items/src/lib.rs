#![allow(dead_code)]
use std::cmp::Ordering;
use std::collections::HashMap;
use types_items::{self as ast, Ast, Evidence, ItemId, TypedVar};

mod pretty;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct VarId(u32);

#[derive(Debug, Eq, PartialEq, Clone)]
struct Var {
  id: VarId,
  ty: Type,
}

impl Var {
  fn new(id: VarId, ty: Type) -> Self {
    Self { id, ty }
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct TypeVar(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
enum Kind {
  Type,
  Row,
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Row {
  Open(TypeVar),
  Closed(Vec<Type>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Type {
  Int,
  Var(TypeVar),
  Fun(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
  Prod(Row),
  Sum(Row),
}

impl Type {
  fn fun(arg: Self, ret: Self) -> Self {
    Self::Fun(Box::new(arg), Box::new(ret))
  }

  fn funs(args: impl Into<Vec<Self>>, ret: Self) -> Self {
    args
      .into()
      .into_iter()
      .rfold(ret, |ret, arg| Self::Fun(Box::new(arg), Box::new(ret)))
  }

  fn ty_fun(kind: Kind, body: Self) -> Self {
    Self::TyFun(kind, Box::new(body))
  }

  fn prod(row: Row) -> Self {
    match row {
      Row::Closed(elems) if elems.len() == 1 => elems.into_iter().next().unwrap(),
      row => Self::Prod(row),
    }
  }

  fn sum(row: Row) -> Self {
    match row {
      Row::Closed(elems) if elems.len() == 1 => elems.into_iter().next().unwrap(),
      row => Self::Sum(row),
    }
  }

  fn subst_row(self, row: Row) -> Self {
    Subst::RowPayload(row).subst_ty(self, 0)
  }

  fn subst_ty(self, ty: Self) -> Self {
    Subst::TyPayload(ty).subst_ty(self, 0)
  }
}

#[derive(Clone)]
enum Subst {
  RowPayload(Row),
  TyPayload(Type),
}
impl Subst {
  fn shift(&mut self) {
    match self {
      Subst::RowPayload(row) => row.shift(),
      Subst::TyPayload(ty) => ty.shift(),
    }
  }

  fn shifted(mut self) -> Self {
    self.shift();
    self
  }

  fn subst_row_var(self) -> Row {
    match self {
      Subst::RowPayload(row) => row,
      Subst::TyPayload(_) => panic!("ICE: Kind mismatch. A type was substituted for a row"),
    }
  }

  fn subst_ty_var(self) -> Type {
    match self {
      Subst::TyPayload(ty) => ty,
      Subst::RowPayload(_) => panic!("ICE: Kind mismatch. A type was substituted for a row"),
    }
  }

  fn subst_row(self, haystack: Row, needle: usize) -> Row {
    match haystack {
      Row::Open(row_var) => match row_var.0.cmp(&needle) {
        Ordering::Equal => self.subst_row_var(),
        Ordering::Less => Row::Open(row_var),
        Ordering::Greater => Row::Open(TypeVar(row_var.0 - 1)),
      },
      Row::Closed(elems) => Row::Closed(
        elems
          .into_iter()
          .map(|elem| self.clone().subst_ty(elem, needle))
          .collect(),
      ),
    }
  }

  fn subst_ty(self, haystack: Type, needle: usize) -> Type {
    match haystack {
      Type::Int => Type::Int,
      Type::Var(type_var) => match type_var.0.cmp(&needle) {
        Ordering::Equal => self.subst_ty_var(),
        Ordering::Less => Type::Var(type_var),
        Ordering::Greater => Type::Var(TypeVar(type_var.0 - 1)),
      },
      Type::Fun(arg, ret) => Type::fun(
        self.clone().subst_ty(*arg, needle),
        self.subst_ty(*ret, needle),
      ),
      Type::TyFun(kind, body) => Type::ty_fun(kind, self.shifted().subst_ty(*body, needle + 1)),
      Type::Prod(row) => Type::prod(self.subst_row(row, needle)),
      Type::Sum(row) => Type::sum(self.subst_row(row, needle)),
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum TyApp {
  Ty(Type),
  Row(Row),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IR {
  Var(Var),
  Int(isize),
  Fun(Var, Box<Self>),
  App(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
  TyApp(Box<Self>, TyApp),
  // Create a product type.
  Tuple(Vec<Self>),
  // Select a field out of a product.
  Field(Box<Self>, usize),
  // Create a sum type.
  Tag(Type, usize, Box<Self>),
  // Case match on a sum.
  Case(Type, Box<Self>, Vec<Branch>),
  Item(Type, ItemId),
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Branch {
  param: Var,
  body: IR,
}

impl Branch {
  fn as_fun(&self) -> IR {
    IR::fun(self.param.clone(), self.body.clone())
  }
}

impl IR {
  fn fun(var: Var, body: Self) -> Self {
    Self::Fun(var, Box::new(body))
  }

  fn funs<I>(vars: I, body: IR) -> IR
  where
    I: IntoIterator<Item = Var>,
    I::IntoIter: DoubleEndedIterator,
  {
    vars.into_iter().rfold(body, |body, var| IR::fun(var, body))
  }

  fn app(fun: Self, arg: Self) -> Self {
    Self::App(Box::new(fun), Box::new(arg))
  }

  fn ty_fun(kind: Kind, ir: Self) -> Self {
    Self::TyFun(kind, Box::new(ir))
  }

  fn ty_app(body: IR, ty: TyApp) -> IR {
    Self::TyApp(Box::new(body), ty)
  }

  fn tuple(elems: impl IntoIterator<Item = Self>) -> IR {
    Self::Tuple(elems.into_iter().collect())
  }

  fn field(body: Self, index: usize) -> Self {
    Self::Field(Box::new(body), index)
  }

  fn tag(ty: Type, tag: usize, body: Self) -> Self {
    Self::Tag(ty, tag, Box::new(body))
  }

  fn case(ty: Type, scrutinee: Self, branch: impl IntoIterator<Item = Branch>) -> Self {
    Self::Case(ty, Box::new(scrutinee), branch.into_iter().collect())
  }

  fn branch(param: Var, body: IR) -> Branch {
    Branch { param, body }
  }

  fn type_of(&self) -> Type {
    match self {
      IR::Var(var) => var.ty.clone(),
      IR::Int(_) => Type::Int,
      IR::Fun(arg, body) => Type::fun(arg.ty.clone(), body.type_of()),
      IR::TyFun(kind, body) => Type::ty_fun(*kind, body.type_of()),
      IR::App(fun, arg) => {
        let Type::Fun(fun_arg_ty, ret_ty) = fun.type_of() else {
          panic!(
            "ICE: IR used non-function type as a function: {}\n{}",
            pretty_string(fun.type_of(), 80),
            pretty_string(self.clone(), 80)
          )
        };
        if arg.type_of() != *fun_arg_ty {
          panic!(
            "ICE: Function applied to wrong argument type {} != {}\n{}",
            pretty_string(arg.type_of(), 80),
            pretty_string(*fun_arg_ty, 80),
            pretty_string(IR::App(fun.clone(), arg.clone()), 80)
          );
        }
        *ret_ty
      }
      IR::TyApp(body, ty_app) => {
        let Type::TyFun(kind, ret_ty) = body.type_of() else {
          panic!("ICE: Type applied to a non-forall IR term");
        };

        match (kind, ty_app) {
          (Kind::Type, TyApp::Ty(ty)) => ret_ty.subst_ty(ty.clone()),
          (Kind::Row, TyApp::Row(row)) => ret_ty.subst_row(row.clone()),
          (Kind::Type, TyApp::Row(_)) => {
            panic!("ICE: Kind mismatch. Type applied a Row to variable of kind Type")
          }
          (Kind::Row, TyApp::Ty(_)) => {
            panic!("ICE: Kind mismatch. Type applied a Type to variable of kind Row")
          }
        }
      }
      IR::Tuple(elems) => Type::Prod(Row::Closed(elems.iter().map(|ir| ir.type_of()).collect())),
      IR::Field(body, field) => {
        let Type::Prod(Row::Closed(elems)) = body.type_of() else {
          panic!("ICE: IR accessed field of a non product type");
        };
        elems[*field].clone()
      }
      IR::Tag(ty, tag, body) => {
        let Type::Sum(Row::Closed(elems)) = ty else {
          panic!("ICE: Tagged value with non sum type");
        };

        if !body.type_of().eq(&elems[*tag]) {
          panic!("ICE: Tagged value has element with the wrong type")
        };

        ty.clone()
      }
      IR::Case(ty, elem, branches) => {
        let Type::Sum(Row::Closed(elems)) = elem.type_of() else {
          panic!("ICE: Case scrutinee does not have sum type")
        };

        for (branch, elem) in branches.iter().zip(elems.iter()) {
          if elem != &branch.param.ty {
            panic!(
              "ICE: Branch has unexpected parameter type {} != {}",
              pretty_string(elem.clone(), 80),
              pretty_string(branch.param.ty.clone(), 80)
            )
          }

          if ty != &branch.body.type_of() {
            panic!("ICE: Branch body has unexpected type")
          }
        }

        ty.clone()
      }
      IR::Item(ty, _) => ty.clone(),
    }
  }
}

#[derive(Default)]
struct VarSupply {
  next: u32,
  cache: HashMap<ast::Var, VarId>,
}

impl VarSupply {
  fn supply_for(&mut self, var: ast::Var) -> VarId {
    self
      .cache
      .entry(var)
      .or_insert_with(|| {
        let ir_var = self.next;
        self.next += 1;
        VarId(ir_var)
      })
      .to_owned()
  }

  fn supply(&mut self) -> VarId {
    let ir_var = self.next;
    self.next += 1;
    VarId(ir_var)
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
enum AstTypeVar {
  Ty(ast::TypeVar),
  Row(ast::RowVar),
}
impl AstTypeVar {
  fn kind(&self) -> Kind {
    match self {
      AstTypeVar::Ty(_) => Kind::Type,
      AstTypeVar::Row(_) => Kind::Row,
    }
  }
}

impl TypeVar {
  fn adjust(&mut self, cutoff: usize) {
    if self.0 >= cutoff {
      self.0 += 1;
    }
  }
}

impl Type {
  fn adjust(&mut self, cutoff: usize) {
    match self {
      Type::Int => {}
      Type::Var(type_var) => type_var.adjust(cutoff),
      Type::Fun(arg, ret) => {
        arg.adjust(cutoff);
        ret.adjust(cutoff);
      }
      Type::TyFun(_, body) => {
        body.adjust(cutoff + 1);
      }
      Type::Prod(row) | Type::Sum(row) => row.adjust(cutoff),
    }
  }

  fn shift(&mut self) {
    self.adjust(0);
  }

  fn shifted(mut self) -> Self {
    self.shift();
    self
  }
}
impl Row {
  fn adjust(&mut self, cutoff: usize) {
    match self {
      Row::Open(type_var) => type_var.adjust(cutoff),
      Row::Closed(tys) => {
        for ty in tys {
          ty.adjust(cutoff);
        }
      }
    }
  }

  fn shift(&mut self) {
    self.adjust(0);
  }
}

type TypeEnv = HashMap<AstTypeVar, TypeVar>;

struct LowerTypes {
  env: TypeEnv,
}
impl LowerTypes {
  fn lower_closed_row_ty(&self, closed_row: ast::ClosedRow) -> Vec<Type> {
    closed_row
      .values
      .into_iter()
      .map(|ty| self.lower_ty(ty))
      .collect()
  }

  fn lower_row_ty(&self, row: ast::Row) -> Row {
    match row {
      ast::Row::Open(var) => {
        let ty_var = self.env[&AstTypeVar::Row(var)];
        Row::Open(ty_var)
      }
      ast::Row::Closed(closed_row) => {
        let values = self.lower_closed_row_ty(closed_row);
        Row::Closed(values)
      }
      ast::Row::Unifier(_) => panic!("ICE: Unexpected row unifier in lowering"),
    }
  }

  fn lower_ty(&self, ty: ast::Type) -> Type {
    match ty {
      ast::Type::Int => Type::Int,
      ast::Type::Var(v) => Type::Var(self.env[&AstTypeVar::Ty(v)]),
      ast::Type::Fun(arg, ret) => {
        let arg = self.lower_ty(*arg);
        let ret = self.lower_ty(*ret);
        Type::fun(arg, ret)
      }
      ast::Type::Prod(row) => Type::prod(self.lower_row_ty(row)),
      ast::Type::Sum(row) => Type::sum(self.lower_row_ty(row)),
      ast::Type::Label(_, ty) => self.lower_ty(*ty),
      ast::Type::Unifier(_) => panic!("ICE: Unexpected type unifier in lowering"),
    }
  }

  fn lower_ev_ty(&self, evidence: ast::Evidence) -> Type {
    match evidence {
      ast::Evidence::RowEquation { left, right, goal } => {
        let left = self.lower_row_ty(left);
        let (left_prod, left_sum) = (Type::prod(left.clone()), Type::sum(left));
        let right = self.lower_row_ty(right);
        let (right_prod, right_sum) = (Type::prod(right.clone()), Type::sum(right));
        let goal = self.lower_row_ty(goal);
        let (goal_prod, goal_sum) = (Type::prod(goal.clone()), Type::sum(goal));

        let concat = Type::funs([left_prod.clone(), right_prod.clone()], goal_prod.clone());
        let branch = {
          let a = TypeVar(0);
          Type::ty_fun(
            Kind::Type,
            Type::funs(
              [
                Type::fun(left_sum.clone().shifted(), Type::Var(a)),
                Type::fun(right_sum.clone().shifted(), Type::Var(a)),
                goal_sum.clone().shifted(),
              ],
              Type::Var(a),
            ),
          )
        };
        let prj_left = Type::fun(goal_prod.clone(), left_prod);
        let inj_left = Type::fun(left_sum, goal_sum.clone());
        let prj_right = Type::fun(goal_prod, right_prod);
        let inj_right = Type::fun(right_sum, goal_sum);
        Type::prod(Row::Closed(vec![
          concat,
          branch,
          Type::prod(Row::Closed(vec![prj_left, inj_left])),
          Type::prod(Row::Closed(vec![prj_right, inj_right])),
        ]))
      }
    }
  }
}

fn lower_ty_scheme(scheme: ast::TypeScheme) -> (Type, Vec<Kind>, LowerTypes) {
  let mut kinds = vec![Kind::Type; scheme.unbound_tys.len() + scheme.unbound_rows.len()];
  let ty_env: TypeEnv = scheme
    .unbound_tys
    .into_iter()
    .map(AstTypeVar::Ty)
    .chain(scheme.unbound_rows.into_iter().map(AstTypeVar::Row))
    .rev()
    .enumerate()
    .map(|(i, tyvar)| {
      kinds[i] = tyvar.kind();
      (tyvar, TypeVar(i))
    })
    .collect();

  let lower = LowerTypes { env: ty_env };

  let lower_ty = lower.lower_ty(scheme.ty);
  let evident_lower_ty = Type::funs(
    scheme
      .evidence
      .into_iter()
      .map(|ev| lower.lower_ev_ty(ev))
      .collect::<Vec<_>>(),
    lower_ty,
  );
  let bound_lower_ty = kinds
    .iter()
    .fold(evident_lower_ty, |ty, kind| Type::ty_fun(*kind, ty));
  (bound_lower_ty, kinds, lower)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum RowIndex {
  Left(usize),
  Right(usize),
}

struct LowerSolvedEv<'a> {
  supply: &'a mut VarSupply,

  left: Vec<Type>,
  right: Vec<Type>,
  goal: Vec<Type>,

  goal_indices: Vec<RowIndex>,
  left_indices: Vec<usize>,
  right_indices: Vec<usize>,
}

fn unwrap_single(len: usize, var: Var, else_fn: impl FnOnce(IR) -> IR) -> IR {
  if len == 1 {
    IR::Var(var)
  } else {
    else_fn(IR::Var(var))
  }
}

// TODO: Figure out where these live and what they should look like
fn unwrap_prj(index: usize, len: usize, prod: Var) -> IR {
  unwrap_single(len, prod, |ir| IR::field(ir, index))
}

impl LowerSolvedEv<'_> {
  fn left_prod(&self) -> Type {
    Type::prod(Row::Closed(self.left.clone()))
  }
  fn right_prod(&self) -> Type {
    Type::prod(Row::Closed(self.right.clone()))
  }
  fn goal_prod(&self) -> Type {
    Type::prod(Row::Closed(self.goal.clone()))
  }

  fn left_sum(&self) -> Type {
    Type::sum(Row::Closed(self.left.clone()))
  }
  fn right_sum(&self) -> Type {
    Type::sum(Row::Closed(self.right.clone()))
  }
  fn goal_sum(&self) -> Type {
    Type::sum(Row::Closed(self.goal.clone()))
  }

  fn make_vars<const N: usize>(&mut self, tys: [Type; N]) -> [Var; N] {
    tys.map(|ty| {
      let id = self.supply.supply();
      Var::new(id, ty)
    })
  }

  fn left_enumerated_values(&self) -> impl Iterator<Item = (usize, Type)> {
    self.left_indices.clone().into_iter().zip(self.left.clone())
  }

  fn right_enumerated_values(&self) -> impl Iterator<Item = (usize, Type)> {
    self
      .right_indices
      .clone()
      .into_iter()
      .zip(self.right.clone())
  }

  fn concat(&mut self) -> IR {
    // TODO: Calculate where these indices go in goal correctly. It's not enough to naively concat
    // like we are here, we need to put them in the right slots.
    let vars = self.make_vars([self.left_prod(), self.right_prod()]);
    IR::funs(vars.clone(), {
      let [left, right] = vars;
      let mut elems = self.goal_indices.iter().map(|row_index| match row_index {
        RowIndex::Left(i) => unwrap_prj(*i, self.left.len(), left.clone()),
        RowIndex::Right(i) => unwrap_prj(*i, self.right.len(), right.clone()),
      });
      if self.goal_indices.len() == 1 {
        elems.next().unwrap()
      } else {
        IR::tuple(elems)
      }
    })
  }

  fn branch(&mut self) -> IR {
    // We have to shift our sum types because because branch introduces a new type variable.
    let left_sum = self.left_sum().shifted();
    let right_sum = self.right_sum().shifted();
    let goal_sum = self.goal_sum().shifted();
    let ret_ty = Type::Var(TypeVar(0));

    let vars = self.make_vars([
      Type::fun(left_sum.clone(), ret_ty.clone()),
      Type::fun(right_sum.clone(), ret_ty.clone()),
      goal_sum,
    ]);
    IR::ty_fun(
      Kind::Type,
      IR::funs(vars.clone(), {
        let [left_var, right_var, goal_var] = vars;
        let goal_len = self.goal.len();
        let mut branches = self.goal_indices.clone().into_iter().map(|row_index| {
          let (i, ty, len, var, sum) = match row_index {
            RowIndex::Left(i) => (
              i,
              self.left[i].clone().shifted(),
              self.left.len(),
              left_var.clone(),
              left_sum.clone(),
            ),
            RowIndex::Right(i) => (
              i,
              self.right[i].clone().shifted(),
              self.right.len(),
              right_var.clone(),
              right_sum.clone(),
            ),
          };
          let [case_var] = self.make_vars([ty]);
          IR::branch(case_var.clone(), {
            IR::app(
              IR::Var(var),
              unwrap_single(len, case_var, |ir| IR::tag(sum, i, ir)),
            )
          })
        });
        if goal_len == 1 {
          IR::app(branches.next().unwrap().as_fun(), IR::Var(goal_var))
        } else {
          IR::case(ret_ty, IR::Var(goal_var), branches)
        }
      }),
    )
  }

  fn prj_left(&mut self) -> IR {
    let [goal] = self.make_vars([self.goal_prod()]);
    IR::fun(goal.clone(), {
      if self.left.len() == 1 {
        unwrap_prj(self.left_indices[0], self.goal.len(), goal)
      } else {
        IR::tuple(
          self
            .left_indices
            .iter()
            .map(|i| unwrap_prj(*i, self.goal.len(), goal.clone())),
        )
      }
    })
  }

  fn prj_right(&mut self) -> IR {
    let [goal] = self.make_vars([self.goal_prod()]);
    IR::fun(goal.clone(), {
      if self.right.len() == 1 {
        unwrap_prj(self.right_indices[0], self.goal.len(), goal)
      } else {
        IR::tuple(
          self
            .right_indices
            .iter()
            .map(|i| unwrap_prj(*i, self.goal.len(), goal.clone())),
        )
      }
    })
  }

  fn inj_left(&mut self) -> IR {
    let [left_var] = self.make_vars([self.left_sum()]);
    IR::fun(left_var.clone(), {
      let branches = self
        .left_enumerated_values()
        .map(|(i, ty)| {
          let [branch_var] = self.make_vars([ty]);
          IR::branch(branch_var.clone(), {
            unwrap_single(self.goal.len(), branch_var, |ir| {
              IR::tag(self.goal_sum(), i, ir)
            })
          })
        })
        .collect::<Vec<_>>();
      if self.left.len() == 1 {
        IR::app(branches[0].as_fun(), IR::Var(left_var))
      } else {
        IR::case(self.goal_sum(), IR::Var(left_var), branches)
      }
    })
  }

  fn inj_right(&mut self) -> IR {
    let [right_var] = self.make_vars([self.right_sum()]);
    IR::fun(right_var.clone(), {
      let branches = self
        .right_enumerated_values()
        .map(|(i, ty)| {
          let [branch_var] = self.make_vars([ty]);
          IR::branch(branch_var.clone(), {
            unwrap_single(self.goal.len(), branch_var, |ir| {
              IR::tag(self.goal_sum(), i, ir)
            })
          })
        })
        .collect::<Vec<_>>();
      if self.right.len() == 1 {
        IR::app(branches[0].as_fun(), IR::Var(right_var))
      } else {
        IR::case(self.goal_sum(), IR::Var(right_var), branches)
      }
    })
  }

  fn lower_ev_term(mut self) -> IR {
    IR::tuple([
      self.concat(),
      self.branch(),
      IR::tuple([self.prj_left(), self.inj_left()]),
      IR::tuple([self.prj_right(), self.inj_right()]),
    ])
  }
}

struct LowerAst {
  supply: VarSupply,
  types: LowerTypes,
  ev_to_var: HashMap<Evidence, Var>,
  item_source: ItemSource,
  solved: Vec<(Var, IR)>,
}

impl LowerAst {
  /// Look up the IR variable that represents the evidence for a given AST node.
  fn lookup_ev(&mut self, ev: Evidence) -> Var {
    // If we've seen this evidence before, reuse the variable we already generated.
    // Otherwise, generate a variable for our solved evidence.
    self
      .ev_to_var
      .entry(ev)
      .or_insert_with_key(|ev| {
        // If we see a vacant entry during lowering it must be solved.
        // All our unsolved evidence appears in the type scheme.
        let Evidence::RowEquation {
          left: ast::Row::Closed(left),
          right: ast::Row::Closed(right),
          goal: ast::Row::Closed(goal),
        } = ev
        else {
          panic!("ICE: Unsolved evidence appeared in AST that wasn't in type scheme");
        };
        let param = self.supply.supply();

        let mut left_indices = vec![0; left.fields.len()];
        let mut right_indices = vec![0; right.fields.len()];
        let goal_indices = goal
          .fields
          .iter()
          .enumerate()
          .map(|(goal_indx, field)| {
            left
              .fields
              .binary_search(field)
              .map(|left_indx| {
                left_indices[left_indx] = goal_indx;
                RowIndex::Left(left_indx)
              })
              .or_else(|_| {
                right.fields.binary_search(field).map(|right_indx| {
                  right_indices[right_indx] = goal_indx;
                  RowIndex::Right(right_indx)
                })
              })
              .expect("ICE: Invalid solved row combination.")
          })
          .collect::<Vec<_>>();

        let left_values = self.types.lower_closed_row_ty(left.clone());
        let right_values = self.types.lower_closed_row_ty(right.clone());
        let goal_values = self.types.lower_closed_row_ty(goal.clone());

        let lower_solved_ev = LowerSolvedEv {
          supply: &mut self.supply,
          left: left_values,
          right: right_values,
          goal: goal_values,
          goal_indices,
          left_indices,
          right_indices,
        };

        let term = lower_solved_ev.lower_ev_term();
        let ty = self.types.lower_ev_ty(ev.clone());
        let var = Var::new(param, ty);
        self.solved.push((var.clone(), term));
        var
      })
      .clone()
  }

  fn lower_ast(&mut self, ast: Ast<TypedVar>) -> IR {
    match ast {
      Ast::Var(TypedVar(var, ty)) => IR::Var(Var::new(
        self.supply.supply_for(var),
        self.types.lower_ty(ty),
      )),
      Ast::Int(i) => IR::Int(i),
      Ast::Fun(TypedVar(var, ty), body) => {
        let ir_ty = self.types.lower_ty(ty);
        let ir_var = self.supply.supply_for(var);
        let ir_body = self.lower_ast(*body);
        IR::fun(Var::new(ir_var, ir_ty), ir_body)
      }
      Ast::App(fun, arg) => {
        let ir_fun = self.lower_ast(*fun);
        let ir_arg = self.lower_ast(*arg);
        IR::app(ir_fun, ir_arg)
      }
      // Labels are only required for type checking.
      // We erase them in the IR.
      Ast::Label(_, body) => self.lower_ast(*body),
      Ast::Unlabel(body, _) => self.lower_ast(*body),
      Ast::Concat(meta, left, right) => {
        let param = meta
          .map(|ev| self.lookup_ev(ev))
          .expect("ICE: Concat AST node lacks an expected evidence");

        let left = self.lower_ast(*left);
        let right = self.lower_ast(*right);
        let concat = IR::field(IR::Var(param), 0);
        IR::app(IR::app(concat, left), right)
      }
      Ast::Project(meta, direction, body) => {
        let param = meta
          .map(|ev| self.lookup_ev(ev))
          .expect("ICE: Project AST node lacks an expected evidence");

        let term = self.lower_ast(*body);
        let direction_field = match direction {
          ast::Direction::Left => 2,
          ast::Direction::Right => 3,
        };
        let prj_direction = IR::field(IR::field(IR::Var(param), direction_field), 0);
        IR::app(prj_direction, term)
      }
      Ast::Branch(meta, left, right) => {
        let meta = meta.expect("ICE: Branch AST node lacks expected meta");
        let param = self.lookup_ev(meta.evidence);

        let ret_ty = self.types.lower_ty(meta.ty);
        let left = self.lower_ast(*left);
        let right = self.lower_ast(*right);
        let branch = IR::ty_app(IR::field(IR::Var(param), 1), TyApp::Ty(ret_ty));
        IR::app(IR::app(branch, left), right)
      }
      Ast::Inject(meta, direction, body) => {
        let param = meta
          .map(|ev| self.lookup_ev(ev))
          .expect("ICE: Inject AST node lacks an expected evidence");

        let term = self.lower_ast(*body);
        let direction_field = match direction {
          ast::Direction::Left => 2,
          ast::Direction::Right => 3,
        };
        let inj_direction = IR::field(IR::field(IR::Var(param), direction_field), 1);
        IR::app(inj_direction, term)
      }
      Ast::Item(wrapper, item_id) => {
        let ty = self.item_source.lookup_item(item_id);
        println!("{}\n{:?}", pretty_string(ty.clone(), 80), wrapper);
        let item_ir = IR::Item(ty, item_id);
        let wrapper = wrapper.expect("ICE: Item lacks expected wrapper");
        let ty_ir = wrapper.types.into_iter().fold(item_ir, |ir, ty| {
          IR::ty_app(ir, TyApp::Ty(self.types.lower_ty(ty)))
        });
        let row_ir = wrapper.rows.into_iter().fold(ty_ir, |ir, row| {
          IR::ty_app(ir, TyApp::Row(self.types.lower_row_ty(row)))
        });
        let ir = wrapper.evidence.into_iter().fold(row_ir, |ir, ev| {
          let param = self.lookup_ev(ev);
          IR::app(ir, IR::Var(param))
        });
        println!("{}", pretty_string(ir.clone(), 80));
        ir
      }
    }
  }
}

struct ItemSource {
  items: HashMap<ItemId, Type>,
}
impl ItemSource {
  fn lookup_item(&self, item: ItemId) -> Type {
    self.items[&item].clone()
  }
}

fn lower_item_source(items: ast::ItemSource) -> ItemSource {
  ItemSource {
    items: items
      .types
      .into_iter()
      .map(|(item_id, ty_scheme)| {
        let (ir_ty, _, _) = lower_ty_scheme(ty_scheme);
        (item_id, ir_ty)
      })
      .collect(),
  }
}

fn lower(ast: Ast<TypedVar>, scheme: ast::TypeScheme) -> (IR, Type) {
  lower_with_items(ast::ItemSource::default(), ast, scheme)
}

fn lower_with_items(
  item_source: ast::ItemSource,
  ast: Ast<TypedVar>,
  scheme: ast::TypeScheme,
) -> (IR, Type) {
  let ev = scheme.evidence.clone();
  let (ir_ty, kinds, lower_ty) = lower_ty_scheme(scheme);

  let mut supply = VarSupply::default();
  let mut ev_to_var: HashMap<ast::Evidence, Var> = HashMap::default();
  let params = ev
    .into_iter()
    .map(|ev| {
      let ty = lower_ty.lower_ev_ty(ev.clone());
      let param = supply.supply();
      let var = Var::new(param, ty);
      ev_to_var.insert(ev, var.clone());
      var
    })
    .collect::<Vec<_>>();

  let mut lower_ast = LowerAst {
    supply,
    types: lower_ty,
    ev_to_var,
    solved: vec![],
    item_source: lower_item_source(item_source),
  };
  let ir = lower_ast.lower_ast(ast);
  let solved_ir = lower_ast
    .solved
    .into_iter()
    .fold(ir, |ir, (var, solved)| IR::app(IR::fun(var, ir), solved));
  let param_ir = params
    .into_iter()
    .rfold(solved_ir, |ir, var| IR::fun(var, ir));
  let bound_ir = kinds
    .into_iter()
    .fold(param_ir, |ir, kind| IR::ty_fun(kind, ir));
  (bound_ir, ir_ty)
}

fn pretty_string<'a>(
  doc: impl ::pretty::Pretty<'a, ::pretty::RcAllocator>,
  width: usize,
) -> String {
  let mut pretty_str = String::new();
  doc
    .pretty(&::pretty::RcAllocator)
    .render_fmt(width, &mut pretty_str)
    .unwrap();
  pretty_str
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_items::{
    self as ast, type_infer, type_infer_with_items, Ast, ClosedRow, RowVar, TypeScheme,
  };

  fn lower_test(ast: Ast<ast::Var>) -> (IR, Type) {
    let (ast, scheme) = type_infer(ast).expect("Type inference to succeed");
    lower(ast, scheme)
  }

  fn lower_item_test(items: ast::ItemSource, ast: Ast<ast::Var>) -> (IR, Type) {
    let (ast, scheme) =
      type_infer_with_items(items.clone(), ast).expect("Type inference to succeed");
    lower_with_items(items, ast, scheme)
  }

  #[test]
  fn lower_int() {
    let ast = Ast::Int(3);

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir, IR::Int(3));
    // Int
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_id_fun() {
    let x = ast::Var(0);
    let ast = Ast::fun(x, Ast::Var(x));

    let (ir, ir_ty) = lower_test(ast);

    let a = Type::Var(TypeVar(0));
    let x = Var::new(VarId(0), a);
    assert_eq!(ir, IR::ty_fun(Kind::Type, IR::fun(x.clone(), IR::Var(x))));
    // forall(fun(Var(a), Var(a)))
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_k_combinator() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let ast = Ast::fun(x, Ast::fun(y, Ast::Var(x)));

    let (ir, ir_ty) = lower_test(ast);

    let a = TypeVar(1);
    let b = TypeVar(0);
    let x = Var::new(VarId(0), Type::Var(a));
    let y = Var::new(VarId(1), Type::Var(b));
    assert_eq!(
      ir,
      IR::ty_fun(
        Kind::Type,
        IR::ty_fun(Kind::Type, IR::fun(x.clone(), IR::fun(y, IR::Var(x))))
      )
    );
    // forall(forall(fun(Var(a), fun(Var(b), Var(a)))))
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_s_combinator() {
    let x = ast::Var(0);
    let y = ast::Var(1);
    let z = ast::Var(2);
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

    let (ir, ir_ty) = lower_test(ast);

    let a = TypeVar(2);
    let b = TypeVar(1);
    let c = TypeVar(0);
    let x = Var::new(
      VarId(0),
      Type::funs([Type::Var(a), Type::Var(b)], Type::Var(c)),
    );
    let y = Var::new(VarId(1), Type::fun(Type::Var(a), Type::Var(b)));
    let z = Var::new(VarId(2), Type::Var(a));
    assert_eq!(
      ir,
      IR::ty_fun(
        Kind::Type,
        IR::ty_fun(
          Kind::Type,
          IR::ty_fun(
            Kind::Type,
            IR::fun(
              x.clone(),
              IR::fun(
                y.clone(),
                IR::fun(
                  z.clone(),
                  IR::app(
                    IR::app(IR::Var(x), IR::Var(z.clone())),
                    IR::app(IR::Var(y), IR::Var(z))
                  )
                )
              )
            )
          )
        )
      )
    );
    // forall(forall(forall(fun(fun(Var(a), fun(Var(b), Var(c))), fun(fun(Var(a), Var(b)), fun(Var(a), Var(c)))))))
    assert_eq!(ir_ty, ir.type_of());
  }

  #[test]
  fn lower_wand_combinator() {
    let m = ast::Var(0);
    let n = ast::Var(1);

    let ast = Ast::fun(
      m,
      Ast::fun(
        n,
        Ast::unlabel(
          Ast::project_(ast::Direction::Left, Ast::concat_(Ast::Var(m), Ast::Var(n))),
          "x",
        ),
      ),
    );

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(
      pretty_string(ir.type_of(), 80),
      pretty_string(ir_ty.clone(), 80)
    );

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          (ty_fun [Row Row Row Row]
            (fun [V0, V1, V2, V3]
              (V1[2][0] (V0[0] V2 V3)))))"#]];
    expect_ir.assert_eq(&pretty_string(ir, 80));

    let expect_ty = expect_test::expect![[r#"
        forall [Type] .
          forall [Row, Row, Row, Row] .
            { {T3} -> {T2} -> {T0}
             , forall [Type] .
               <T4> -> T0 -> <T3> -> T0 -> <T1> -> T0
             , {{T0} -> {T3}, <T3> -> <T0>}
             , {{T0} -> {T2}, <T2> -> <T0>}
            } -> { T4 -> {T1} -> {T0}
                  , forall [Type] .
                    T5 -> T0 -> <T2> -> T0 -> <T1> -> T0
                  , {{T0} -> T4, T4 -> <T0>}
                  , {{T0} -> {T1}, <T1> -> <T0>}
            } -> {T3} -> {T2} -> T4"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }

  #[test]
  fn lower_big_product() {
    let m = ast::Var(0);
    let ast = Ast::concat_(
      Ast::concat_(Ast::label("x", Ast::Int(1)), Ast::label("y", Ast::Int(2))),
      Ast::concat_(
        Ast::label("a", Ast::fun(m, Ast::Var(m))),
        Ast::label("z", Ast::Int(3)),
      ),
    );

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir.type_of(), ir_ty);

    // Haha, oh god. We can't get to inlining fast enough.
    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          ((fun [V32]
            ((fun [V18]
              ((fun [V0]
                (V0[0] (V18[0] 1 2) (V32[0] (fun [V46] V46) 3)))
                { (fun [V1, V2]
                  {V2[0], V1[0], V1[1], V2[1]})
                , (ty_fun [Type]
                  (fun [V3, V4, V5]
                    (case [V5] [
                      V6 => (V4 <0: V6>)
                      V7 => (V3 <0: V7>)
                      V8 => (V3 <1: V8>)
                      V9 => (V4 <1: V9>)
                      ])))
                , { (fun [V10]
                    {V10[1], V10[2]})
                  , (fun [V11]
                    (case [V11] [
                      V12 => <1: V12>
                      V13 => <2: V13>
                      ]))
                  }
                , { (fun [V14]
                    {V14[0], V14[3]})
                  , (fun [V15]
                    (case [V15] [
                      V16 => <0: V16>
                      V17 => <3: V17>
                      ]))
                  }
                }))
              { (fun [V19, V20]
                {V19, V20})
              , (ty_fun [Type]
                (fun [V21, V22, V23]
                  (case [V23] [
                    V24 => (V21 V24)
                    V25 => (V22 V25)
                    ])))
              , {(fun [V26] V26[0]), (fun [V27] ((fun [V28] <0: V28>) V27))}
              , {(fun [V29] V29[1]), (fun [V30] ((fun [V31] <1: V31>) V30))}
              }))
            { (fun [V33, V34]
              {V33, V34})
            , (ty_fun [Type]
              (fun [V35, V36, V37]
                (case [V37] [
                  V38 => (V35 V38)
                  V39 => (V36 V39)
                  ])))
            , {(fun [V40] V40[0]), (fun [V41] ((fun [V42] <0: V42>) V41))}
            , {(fun [V43] V43[1]), (fun [V44] ((fun [V45] <1: V45>) V44))}
            }))"#]];
    expect_ir.assert_eq(&pretty_string(ir, 80));

    // How can so much IR make such small type.
    let expect_ty = expect_test::expect![[r#"
        forall [Type] .
          {T0 -> T0, Int, Int, Int}"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }

  #[test]
  fn lower_big_sum() {
    let ast = Ast::branch_(
      Ast::branch_(
        Ast::fun(ast::Var(0), Ast::unlabel(Ast::Var(ast::Var(0)), "x")),
        Ast::fun(ast::Var(1), Ast::unlabel(Ast::Var(ast::Var(1)), "y")),
      ),
      Ast::branch_(
        Ast::fun(
          ast::Var(2),
          Ast::app(Ast::unlabel(Ast::Var(ast::Var(2)), "a"), Ast::Int(1)),
        ),
        Ast::fun(ast::Var(3), Ast::unlabel(Ast::Var(ast::Var(3)), "z")),
      ),
    );

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir.type_of(), ir_ty);

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          ((fun [V34]
            ((fun [V18]
              ((fun [V0]
                ((ty_app [V0[1]] Ty(T0))
                  ((ty_app [V18[1]] Ty(T0))
                    (fun [V32]
                      V32) (fun [V33]
                      V33)) ((ty_app [V34[1]] Ty(T0))
                    (fun [V48]
                      (V48 1)) (fun [V49]
                      V49))))
                { (fun [V1, V2]
                  {V2[0], V1[0], V1[1], V2[1]})
                , (ty_fun [Type]
                  (fun [V3, V4, V5]
                    (case [V5] [
                      V6 => (V4 <0: V6>)
                      V7 => (V3 <0: V7>)
                      V8 => (V3 <1: V8>)
                      V9 => (V4 <1: V9>)
                      ])))
                , { (fun [V10]
                    {V10[1], V10[2]})
                  , (fun [V11]
                    (case [V11] [
                      V12 => <1: V12>
                      V13 => <2: V13>
                      ]))
                  }
                , { (fun [V14]
                    {V14[0], V14[3]})
                  , (fun [V15]
                    (case [V15] [
                      V16 => <0: V16>
                      V17 => <3: V17>
                      ]))
                  }
                }))
              { (fun [V19, V20]
                {V19, V20})
              , (ty_fun [Type]
                (fun [V21, V22, V23]
                  (case [V23] [
                    V24 => (V21 V24)
                    V25 => (V22 V25)
                    ])))
              , {(fun [V26] V26[0]), (fun [V27] ((fun [V28] <0: V28>) V27))}
              , {(fun [V29] V29[1]), (fun [V30] ((fun [V31] <1: V31>) V30))}
              }))
            { (fun [V35, V36]
              {V35, V36})
            , (ty_fun [Type]
              (fun [V37, V38, V39]
                (case [V39] [
                  V40 => (V37 V40)
                  V41 => (V38 V41)
                  ])))
            , {(fun [V42] V42[0]), (fun [V43] ((fun [V44] <0: V44>) V43))}
            , {(fun [V45] V45[1]), (fun [V46] ((fun [V47] <1: V47>) V46))}
            }))"#]];
    expect_ir.assert_eq(&pretty_string(ir, 80));

    let expect_ty = expect_test::expect![[r#"
        forall [Type] .
          <Int -> T0, T0, T0, T0> -> T0"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }

  macro_rules! set {
        () => {{ std::collections::BTreeSet::new() }};
        ($($ele:expr),*) => {{
            let mut tmp = std::collections::BTreeSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

  #[test]
  fn lower_items() {
    let items = ast::ItemSource::from_iter([(
      ItemId(0),
      TypeScheme {
        unbound_rows: set![RowVar(9), RowVar(11)],
        unbound_tys: set![ast::TypeVar(3)],
        evidence: vec![Evidence::RowEquation {
          left: ast::Row::Open(RowVar(9)),
          right: ast::Row::Closed(ClosedRow {
            fields: vec!["x".to_string()],
            values: vec![ast::Type::Var(ast::TypeVar(3))],
          }),
          goal: ast::Row::Open(RowVar(11)),
        }],
        ty: ast::Type::fun(
          ast::Type::Prod(ast::Row::Open(RowVar(9))),
          ast::Type::fun(
            ast::Type::Var(ast::TypeVar(3)),
            ast::Type::Prod(ast::Row::Open(RowVar(11))),
          ),
        ),
      },
    )]);
    let ast = Ast::app(
      Ast::app(
        Ast::Item(None, ItemId(0)),
        Ast::concat_(Ast::label("y", Ast::Int(4)), Ast::label("z", Ast::Int(6))),
      ),
      Ast::fun(ast::Var(0), Ast::Var(ast::Var(0))),
    );

    let (ir, ir_ty) = lower_item_test(items, ast);

    assert_eq!(ir.type_of(), ir_ty);

    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          ((fun [V16]
            ((fun [V0]
              ((ty_app [item0] Ty(T0 -> T0) Row(Int, Int) Row(T0 -> T0, Int, Int))
                V0 (V16[0] 4 6) (fun [V30]
                  V30)))
              { (fun [V1, V2]
                {V2, V1[0], V1[1]})
              , (ty_fun [Type]
                (fun [V3, V4, V5]
                  (case [V5] [
                    V6 => (V4 V6)
                    V7 => (V3 <0: V7>)
                    V8 => (V3 <1: V8>)
                    ])))
              , { (fun [V9]
                  {V9[1], V9[2]})
                , (fun [V10]
                  (case [V10] [
                    V11 => <1: V11>
                    V12 => <2: V12>
                    ]))
                }
              , {(fun [V13] V13[0]), (fun [V14] ((fun [V15] <0: V15>) V14))}
              }))
            { (fun [V17, V18]
              {V17, V18})
            , (ty_fun [Type]
              (fun [V19, V20, V21]
                (case [V21] [
                  V22 => (V19 V22)
                  V23 => (V20 V23)
                  ])))
            , {(fun [V24] V24[0]), (fun [V25] ((fun [V26] <0: V26>) V25))}
            , {(fun [V27] V27[1]), (fun [V28] ((fun [V29] <1: V29>) V28))}
            }))"#]];
    expect_ir.assert_eq(&pretty_string(ir, 80));

    let expect_ty = expect_test::expect![[r#"
        forall [Type] .
          {T0 -> T0, Int, Int}"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }
  // TODO: Write tests for items.
  // * Check that calling item works as expected with wrapper.
  // * Especially check order of applications in wrapper.
}
