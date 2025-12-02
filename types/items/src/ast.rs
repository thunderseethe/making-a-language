use crate::ty::{Row, Type};
use crate::Evidence;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct Var(pub usize);

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct TypedVar(pub Var, pub Type);

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Copy, Hash)]
pub struct NodeId(pub u32);

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
  Var(NodeId, V),
  /// An integer literal
  Int(NodeId, i32),
  /// A function literal (lambda, closure).
  Fun(NodeId, V, Box<Self>),
  /// Function application
  App(NodeId, Box<Self>, Box<Self>),
  // --- Row Nodes ---
  // Label a node turning it into a singleton row
  Label(NodeId, Label, Box<Self>),
  // Unwrap a singleton row into it's underlying value
  Unlabel(NodeId, Box<Self>, Label),
  // Concat two products
  Concat(NodeId, Box<Self>, Box<Self>),
  // Project a product into a sub product
  Project(NodeId, Direction, Box<Self>),
  // Branch on a sum type to two handler functions
  Branch(NodeId, Box<Self>, Box<Self>),
  // Inject a value into a sum type
  Inject(NodeId, Direction, Box<Self>),
  // A reference to a top level definition
  Item(NodeId, ItemId),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ItemWrapper {
  pub types: Vec<Type>,
  pub rows: Vec<Row>,
  pub evidence: Vec<Evidence>,
}

impl<V> Ast<V> {
  pub(crate) fn id(&self) -> NodeId {
    match self {
      Ast::Var(node_id, _)
      | Ast::Int(node_id, _)
      | Ast::Fun(node_id, _, _)
      | Ast::App(node_id, _, _)
      | Ast::Label(node_id, _, _)
      | Ast::Unlabel(node_id, _, _)
      | Ast::Concat(node_id, _, _)
      | Ast::Project(node_id, _, _)
      | Ast::Branch(node_id, _, _)
      | Ast::Inject(node_id, _, _)
      | Ast::Item(node_id, _) => *node_id,
    }
  }

  pub fn fun(node_id: NodeId, arg: V, body: Self) -> Self {
    Self::Fun(node_id, arg, Box::new(body))
  }

  pub fn app(node_id: NodeId, fun: Self, arg: Self) -> Self {
    Self::App(node_id, Box::new(fun), Box::new(arg))
  }

  pub fn label(node_id: NodeId, label: impl ToString, value: Self) -> Self {
    Self::Label(node_id, label.to_string(), Box::new(value))
  }

  pub fn unlabel(node_id: NodeId, value: Self, label: impl ToString) -> Self {
    Self::Unlabel(node_id, Box::new(value), label.to_string())
  }

  pub fn project(node_id: NodeId, dir: Direction, value: Self) -> Self {
    Self::Project(node_id, dir, Box::new(value))
  }

  pub fn concat(node_id: NodeId, left: Self, right: Self) -> Self {
    Self::Concat(node_id, Box::new(left), Box::new(right))
  }

  pub fn inject(node_id: NodeId, dir: Direction, value: Self) -> Self {
    Self::Inject(node_id, dir, Box::new(value))
  }

  pub fn branch(node_id: NodeId, left: Self, right: Self) -> Self {
    Self::Branch(node_id, Box::new(left), Box::new(right))
  }
}
