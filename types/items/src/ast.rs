use crate::ty::{Type, Row};
use crate::Evidence;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct Var(pub usize);

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct TypedVar(pub Var, pub Type);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct ItemId(pub usize);

/// Our labels are strings, but we could imagine in a production grade compiler labels would be
/// interned and represented by their intern token.
pub type Label = String;

/// Direction of our row for Project and Inject.
/// Determines where our value shows up in our row combination (in the left or right slot).
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Direction {
  Left,
  Right,
}

/// Our Abstract syntax tree
/// The lambda calculus + integer literals.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Ast<V> {
  /// A local variable
  Var(V),
  /// An integer literal
  Int(isize),
  /// A function literal (lambda, closure).
  Fun(V, Box<Self>),
  /// Function application
  App(Box<Self>, Box<Self>),
  // --- Row Nodes ---
  // Label a node turning it into a singleton row
  Label(Label, Box<Self>),
  // Unwrap a singleton row into it's underlying value
  Unlabel(Box<Self>, Label),
  // Concat two products
  Concat(Option<Evidence>, Box<Self>, Box<Self>),
  // Project a product into a sub product
  Project(Option<Evidence>, Direction, Box<Self>),
  // Branch on a sum type to two handler functions
  Branch(Option<BranchMeta>, Box<Self>, Box<Self>),
  // Inject a value into a sum type
  Inject(Option<Evidence>, Direction, Box<Self>),
  // A reference to a top level definition
  Item(Option<ItemWrapper>, ItemId)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct BranchMeta {
  pub evidence: Evidence,
  pub ty: Type
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ItemWrapper {
  pub types: Vec<Type>,
  pub rows: Vec<Row>,
  pub evidence: Vec<Evidence>
}

impl<V> Ast<V> {
  pub fn fun(arg: V, body: Self) -> Self {
    Self::Fun(arg, Box::new(body))
  }

  pub fn app(fun: Self, arg: Self) -> Self {
    Self::App(Box::new(fun), Box::new(arg))
  }

  pub fn label(label: impl ToString, value: Self) -> Self {
    Self::Label(label.to_string(), Box::new(value))
  }

  pub fn unlabel(value: Self, label: impl ToString) -> Self {
    Self::Unlabel(Box::new(value), label.to_string())
  }

  pub fn project(meta: Evidence, dir: Direction, value: Self) -> Self {
    Self::Project(Some(meta), dir, Box::new(value))
  }

  pub fn concat(meta: Evidence, left: Self, right: Self) -> Self {
    Self::Concat(Some(meta), Box::new(left), Box::new(right))
  }

  pub fn inject(meta: Evidence, dir: Direction, value: Self) -> Self {
    Self::Inject(Some(meta), dir, Box::new(value))
  }

  pub fn branch(meta: BranchMeta, left: Self, right: Self) -> Self {
    Self::Branch(Some(meta), Box::new(left), Box::new(right))
  }
}

impl Ast<Var> {
  pub fn project_(dir: Direction, value: Self) -> Self {
    Self::Project(None, dir, Box::new(value))
  }

  pub fn concat_(left: Self, right: Self) -> Self {
    Self::Concat(None, Box::new(left), Box::new(right))
  }

  pub fn inject_(dir: Direction, value: Self) -> Self {
    Self::Inject(None, dir, Box::new(value))
  }

  pub fn branch_(left: Self, right: Self) -> Self {
    Self::Branch(None, Box::new(left), Box::new(right))
  }
}
