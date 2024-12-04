#![allow(dead_code)]
use std::cmp::Ordering;
use std::collections::HashMap;
use types_rows::{self as ast, Ast, Evidence, TypedVar};

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
enum Type {
  Int,
  Var(TypeVar),
  Fun(Box<Self>, Box<Self>),
  Forall(Kind, Box<Self>),
  Prod(Vec<Self>),
  Sum(Vec<Self>),
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

  fn forall(kind: Kind, body: Self) -> Self {
    Self::Forall(kind, Box::new(body))
  }

  fn prod(elems: Vec<Self>) -> Self
  {
    if elems.len() == 1 {
      elems.into_iter().next().unwrap()
    } else {
      Self::Prod(elems)
    }
  }

  fn sum(elems: Vec<Self>) -> Self {
    if elems.len() == 1 {
      elems.into_iter().next().unwrap()
    } else {
      Self::Sum(elems)
    }
  }

  fn subst_internal(self, ty: Self, needle: usize) -> Self {
    match self {
      Type::Int => Type::Int,
      Type::Var(type_var) => match type_var.0.cmp(&needle) {
        Ordering::Equal => ty,
        Ordering::Less => Type::Var(type_var),
        Ordering::Greater => Type::Var(TypeVar(type_var.0 - 1)),
      },
      Type::Fun(arg, ret) => Type::fun(arg.subst(ty.clone()), ret.subst(ty)),
      Type::Forall(kind, body) => Type::forall(kind, body.subst_internal(ty, needle + 1)),
      Type::Prod(elems) => Type::prod(
        elems
          .into_iter()
          .map(|elem| elem.subst_internal(ty.clone(), needle))
          .collect(),
      ),
      Type::Sum(elems) => Type::sum(
        elems
          .into_iter()
          .map(|elem| elem.subst_internal(ty.clone(), needle))
          .collect(),
      ),
    }
  }

  fn subst(self, ty: Self) -> Self {
    self.subst_internal(ty, 0)
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum IR {
  Var(Var),
  Int(isize),
  Fun(Var, Box<Self>),
  App(Box<Self>, Box<Self>),
  TyFun(Kind, Box<Self>),
  TyApp(Box<Self>, Type),
  // Create a product type.
  Tuple(Vec<Self>),
  // Select a field out of a product.
  Field(Box<Self>, usize),
  // Create a sum type.
  Tag(Type, usize, Box<Self>),
  // Case match on a sum.
  Case(Type, Box<Self>, Vec<Branch>),
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

  fn ty_app(body: IR, ty: Type) -> IR {
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
      IR::App(fun, arg) => {
        let Type::Fun(fun_arg_ty, ret_ty) = fun.type_of() else {
          panic!(
            "ICE: IR used non-function type as a function: {}\n{}",
            pretty_string(fun.type_of(), 80),
            pretty_string(self.clone(), 80)
          )
        };
        let arg_ty = arg.type_of();
        if arg_ty != *fun_arg_ty {
          panic!(
            "ICE: Function applied to wrong argument type:\n{:?}\n{:?}",
            arg_ty, fun_arg_ty
          );
        }
        *ret_ty
      }
      IR::TyFun(kind, body) => Type::forall(*kind, body.type_of()),
      IR::TyApp(body, ty) => {
        let Type::Forall(_, body_ty) = body.type_of() else {
          panic!("ICE: Type applied to a non-forall IR term");
        };

        body_ty.subst(ty.clone())
      }
      IR::Tuple(elems) => Type::Prod(elems.iter().map(|ir| ir.type_of()).collect()),
      IR::Field(body, field) => {
        let Type::Prod(elems) = body.type_of() else {
          panic!("ICE: IR accessed field of a non product type");
        };
        elems[*field].clone()
      }
      IR::Tag(ty, tag, body) => {
        let Type::Sum(elems) = ty else {
          panic!("ICE: Tagged value with non sum type");
        };

        if !body.type_of().eq(&elems[*tag]) {
          panic!("ICE: Tagged value has element with the wrong type")
        };

        ty.clone()
      }
      IR::Case(ty, elem, branches) => {
        let Type::Sum(elems) = elem.type_of() else {
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
      Type::Forall(_, body) => {
        body.adjust(cutoff + 1);
      }
      Type::Prod(elems) | Type::Sum(elems) => elems.iter_mut().for_each(|ty| ty.adjust(cutoff)),
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

  fn lower_row_ty(&self, row: ast::Row) -> (Type, Type) {
    match row {
      ast::Row::Open(var) => {
        let ty_var = self.env[&AstTypeVar::Row(var)];
        (Type::Var(ty_var), Type::Var(ty_var))
      }
      ast::Row::Closed(closed_row) => {
        let values = self.lower_closed_row_ty(closed_row);
        (Type::prod(values.clone()), Type::sum(values))
      }
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
      ast::Type::Prod(row) => {
        let (ty, _) = self.lower_row_ty(row);
        ty
      }
      ast::Type::Sum(row) => {
        let (_, ty) = self.lower_row_ty(row);
        ty
      }
      ast::Type::Label(_, ty) => self.lower_ty(*ty),
    }
  }

  fn lower_ev_ty(&self, evidence: ast::Evidence) -> Type {
    match evidence {
      ast::Evidence::RowEquation { left, right, goal } => {
        let (left_prod, left_sum) = self.lower_row_ty(left);
        let (right_prod, right_sum) = self.lower_row_ty(right);
        let (goal_prod, goal_sum) = self.lower_row_ty(goal);

        let concat = Type::funs([left_prod.clone(), right_prod.clone()], goal_prod.clone());
        let branch = {
          let a = TypeVar(0);
          Type::forall(
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
        Type::prod(vec![
          concat,
          branch,
          Type::prod(vec![prj_left, inj_left]),
          Type::prod(vec![prj_right, inj_right]),
        ])
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
  let lower_ty = Type::funs(
    scheme
      .evidence
      .into_iter()
      .map(|ev| lower.lower_ev_ty(ev))
      .collect::<Vec<_>>(),
    lower_ty,
  );
  let lower_ty = kinds
    .iter()
    .fold(lower_ty, |ty, kind| Type::forall(*kind, ty));
  (lower_ty, kinds, lower)
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
    Type::prod(self.left.clone())
  }
  fn right_prod(&self) -> Type {
    Type::prod(self.right.clone())
  }
  fn goal_prod(&self) -> Type {
    Type::prod(self.goal.clone())
  }

  fn left_sum(&self) -> Type {
    Type::sum(self.left.clone())
  }
  fn right_sum(&self) -> Type {
    Type::sum(self.right.clone())
  }
  fn goal_sum(&self) -> Type {
    Type::sum(self.goal.clone())
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
  ast_to_ev: HashMap<Ast<TypedVar>, (ast::Evidence, ast::Type)>,
  ev_to_var: HashMap<Evidence, Var>,
}

impl LowerAst {
  /// Look up the IR variable that represents the evidence for a given AST node.
  fn lookup_ev(&self, ast: &Ast<TypedVar>) -> Option<(Var, ast::Type)> {
    let (ev, ty) = self.ast_to_ev.get(ast)?;
    let param = self.ev_to_var.get(ev)?.clone();
    Some((param, ty.clone()))
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
      Ast::Concat(left, right) => {
        let (param, _) = self
          .lookup_ev(&Ast::Concat(left.clone(), right.clone()))
          .expect("ICE: Concat AST node lacks an expected evidence");

        let left = self.lower_ast(*left);
        let right = self.lower_ast(*right);
        let concat = IR::field(IR::Var(param), 0);
        IR::app(IR::app(concat, left), right)
      }
      Ast::Project(direction, body) => {
        let (param, _) = self
          .lookup_ev(&Ast::Project(direction, body.clone()))
          .expect("ICE: Project AST node lacks an expected evidence");

        let term = self.lower_ast(*body);
        let direction_field = match direction {
          ast::Direction::Left => 2,
          ast::Direction::Right => 3,
        };
        let prj_direction = IR::field(IR::field(IR::Var(param), direction_field), 0);
        IR::app(prj_direction, term)
      }
      Ast::Branch(left, right) => {
        let (param, ty) = self
          .lookup_ev(&Ast::Branch(left.clone(), right.clone()))
          .expect("ICE: Branch AST node lacks an expected evidence");

        let ret_ty = self.types.lower_ty(ty);
        let left = self.lower_ast(*left);
        let right = self.lower_ast(*right);
        let branch = IR::ty_app(IR::field(IR::Var(param), 1), ret_ty);
        IR::app(IR::app(branch, left), right)
      }
      Ast::Inject(direction, body) => {
        let (param, _) = self
          .lookup_ev(&Ast::Inject(direction, body.clone()))
          .expect("ICE: Inject AST node lacks an expected evidence");

        let term = self.lower_ast(*body);
        let direction_field = match direction {
          ast::Direction::Left => 2,
          ast::Direction::Right => 3,
        };
        let inj_direction = IR::field(IR::field(IR::Var(param), direction_field), 1);
        IR::app(inj_direction, term)
      }
    }
  }
}

fn create_locals_for_solved_ev(
  lower_ty: &LowerTypes,
  ast_to_ev: &HashMap<Ast<TypedVar>, (ast::Evidence, ast::Type)>,
  supply: &mut VarSupply,
  ev_to_var: &mut HashMap<ast::Evidence, Var>,
) -> Vec<(Var, IR)> {
  let mut solved = vec![];
  let mut evs = ast_to_ev.values().cloned().collect::<Vec<_>>();
  // We sort our vector so that our variable generation isn't reliant on the order of the hash map.
  // This makes testing more deterministic since hash order will change between test runs.
  evs.sort();
  for (ev, _) in evs {
    // Any unsolved evidence would've appeared in our type scheme, so we only have to handle solved
    // evidence here.
    if let ast::Evidence::RowEquation {
      left: ast::Row::Closed(left),
      right: ast::Row::Closed(right),
      goal: ast::Row::Closed(goal),
    } = ev.clone()
    {
      ev_to_var.entry(ev.clone()).or_insert_with(|| {
        let param = supply.supply();

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

        let left_values = lower_ty.lower_closed_row_ty(left.clone());
        let right_values = lower_ty.lower_closed_row_ty(right.clone());
        let goal_values = lower_ty.lower_closed_row_ty(goal);

        let lower_solved_ev = LowerSolvedEv {
          supply,
          left: left_values,
          right: right_values,
          goal: goal_values,
          goal_indices,
          left_indices,
          right_indices,
        };

        let term = lower_solved_ev.lower_ev_term();
        let ty = lower_ty.lower_ev_ty(ev.clone());
        let var = Var::new(param, ty);
        solved.push((var.clone(), term));
        var
      });
    }
  }
  solved
}

fn lower(
  ast: Ast<TypedVar>,
  scheme: ast::TypeScheme,
  ast_to_ev: HashMap<Ast<TypedVar>, (ast::Evidence, ast::Type)>,
) -> (IR, Type) {
  let mut supply = VarSupply::default();
  let ev = scheme.evidence.clone();
  let (ir_ty, kinds, lower_ty) = lower_ty_scheme(scheme);

  let mut ev_to_var: HashMap<types_rows::Evidence, Var> = HashMap::default();
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

  let solved = create_locals_for_solved_ev(&lower_ty, &ast_to_ev, &mut supply, &mut ev_to_var);

  let mut lower_ast = LowerAst {
    supply,
    types: lower_ty,
    ast_to_ev,
    ev_to_var,
  };
  let ir = lower_ast.lower_ast(ast);
  let ir = solved
    .into_iter()
    .fold(ir, |ir, (var, solved)| IR::app(IR::fun(var, ir), solved));
  let ir = params.into_iter().rfold(ir, |ir, var| IR::fun(var, ir));
  let ir = kinds.into_iter().fold(ir, |ir, kind| IR::ty_fun(kind, ir));
  (ir, ir_ty)
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
  use types_rows::{self as ast, type_infer, Ast};

  fn lower_test(ast: Ast<ast::Var>) -> (IR, Type) {
    let (ast, scheme, ast_to_ev) = type_infer(ast).expect("Type inference to succeed");
    lower(ast, scheme, ast_to_ev)
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
          Ast::project(ast::Direction::Left, Ast::concat(Ast::Var(m), Ast::Var(n))),
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
            { T1 -> T0 -> T3
            , forall [Type] .
              T2 -> T0 -> T1 -> T0 -> T4 -> T0
            , {T3 -> T1, T1 -> T3}
            , {T3 -> T0, T0 -> T3}
            } -> { T4 -> T2 -> T3
                 , forall [Type] .
                   T5 -> T0 -> T3 -> T0 -> T4 -> T0
                 , {T3 -> T4, T4 -> T3}
                 , {T3 -> T2, T2 -> T3}
                 } -> T1 -> T0 -> T4"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }

  #[test]
  fn lower_big_product() {
    let m = ast::Var(0);
    let ast = Ast::concat(
      Ast::concat(Ast::label("x", Ast::Int(1)), Ast::label("y", Ast::Int(2))),
      Ast::concat(
        Ast::label("a", Ast::fun(m, Ast::Var(m))),
        Ast::label("z", Ast::Int(3)),
      ),
    );

    let (ir, ir_ty) = lower_test(ast);

    assert_eq!(ir.type_of(), ir_ty);

    // Haha, oh god.
    let expect_ir = expect_test::expect![[r#"
        (ty_fun [Type]
          ((fun [V28]
            ((fun [V14]
              ((fun [V0]
                (V28[0] (V14[0] 1 2) (V0[0] (fun [V46] V46) 3)))
                { (fun [V1, V2]
                  {V1, V2})
                , (ty_fun [Type]
                  (fun [V3, V4, V5]
                    (case [V5] [
                      V6 => (V3 V6)
                      V7 => (V4 V7)
                      ])))
                , {(fun [V8] V8[0]), (fun [V9] ((fun [V10] <0: V10>) V9))}
                , {(fun [V11] V11[1]), (fun [V12] ((fun [V13] <1: V13>) V12))}
                }))
              { (fun [V15, V16]
                {V15, V16})
              , (ty_fun [Type]
                (fun [V17, V18, V19]
                  (case [V19] [
                    V20 => (V17 V20)
                    V21 => (V18 V21)
                    ])))
              , {(fun [V22] V22[0]), (fun [V23] ((fun [V24] <0: V24>) V23))}
              , {(fun [V25] V25[1]), (fun [V26] ((fun [V27] <1: V27>) V26))}
              }))
            { (fun [V29, V30]
              {V30[0], V29[0], V29[1], V30[1]})
            , (ty_fun [Type]
              (fun [V31, V32, V33]
                (case [V33] [
                  V34 => (V32 <0: V34>)
                  V35 => (V31 <0: V35>)
                  V36 => (V31 <1: V36>)
                  V37 => (V32 <1: V37>)
                  ])))
            , { (fun [V38]
                {V38[1], V38[2]})
              , (fun [V39]
                (case [V39] [
                  V40 => <1: V40>
                  V41 => <2: V41>
                  ]))
              }
            , { (fun [V42]
                {V42[0], V42[3]})
              , (fun [V43]
                (case [V43] [
                  V44 => <0: V44>
                  V45 => <3: V45>
                  ]))
              }
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
    let ast = Ast::branch(
      Ast::branch(
        Ast::fun(ast::Var(0), Ast::unlabel(Ast::Var(ast::Var(0)), "x")),
        Ast::fun(ast::Var(1), Ast::unlabel(Ast::Var(ast::Var(1)), "y")),
      ),
      Ast::branch(
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
          ((fun [V28]
            ((fun [V14]
              ((fun [V0]
                ((ty_app [V28[1]] T0)
                  ((ty_app [V14[1]] T0)
                    (fun [V46]
                      V46) (fun [V47]
                      V47)) ((ty_app [V0[1]] T0) (fun [V48] (V48 1)) (fun [V49] V49))))
                { (fun [V1, V2]
                  {V1, V2})
                , (ty_fun [Type]
                  (fun [V3, V4, V5]
                    (case [V5] [
                      V6 => (V3 V6)
                      V7 => (V4 V7)
                      ])))
                , {(fun [V8] V8[0]), (fun [V9] ((fun [V10] <0: V10>) V9))}
                , {(fun [V11] V11[1]), (fun [V12] ((fun [V13] <1: V13>) V12))}
                }))
              { (fun [V15, V16]
                {V15, V16})
              , (ty_fun [Type]
                (fun [V17, V18, V19]
                  (case [V19] [
                    V20 => (V17 V20)
                    V21 => (V18 V21)
                    ])))
              , {(fun [V22] V22[0]), (fun [V23] ((fun [V24] <0: V24>) V23))}
              , {(fun [V25] V25[1]), (fun [V26] ((fun [V27] <1: V27>) V26))}
              }))
            { (fun [V29, V30]
              {V30[0], V29[0], V29[1], V30[1]})
            , (ty_fun [Type]
              (fun [V31, V32, V33]
                (case [V33] [
                  V34 => (V32 <0: V34>)
                  V35 => (V31 <0: V35>)
                  V36 => (V31 <1: V36>)
                  V37 => (V32 <1: V37>)
                  ])))
            , { (fun [V38]
                {V38[1], V38[2]})
              , (fun [V39]
                (case [V39] [
                  V40 => <1: V40>
                  V41 => <2: V41>
                  ]))
              }
            , { (fun [V42]
                {V42[0], V42[3]})
              , (fun [V43]
                (case [V43] [
                  V44 => <0: V44>
                  V45 => <3: V45>
                  ]))
              }
            }))"#]];
    expect_ir.assert_eq(&pretty_string(ir, 80));

    let expect_ty = expect_test::expect![[r#"
        forall [Type] .
          <Int -> T0, T0, T0, T0> -> T0"#]];
    expect_ty.assert_eq(&pretty_string(ir_ty, 80));
  }
}
