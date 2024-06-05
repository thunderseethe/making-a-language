use crate::ty::Type;

#[derive(
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Clone,
  Copy,
  Debug,
  Hash,
)]
pub struct Var(pub usize);

#[derive(
  PartialEq, Eq, Clone, Debug,
)]
pub struct TypedVar(
  pub Var,
  pub Type,
);

/// Our labels are strings, but we could imagine in a production grade compiler labels would be
/// interned and represented by their intern token.
pub type Label = String;

/// Direction of our row for Project and Inject.
/// Determines where our value shows up in our row combination (in the left or right slot).
#[derive(
  Debug, PartialEq, Eq,
)]
pub enum Direction {
  Left,
  Right,
}

/// Our Abstract syntax tree
/// The lambda calculus + integer literals.
#[derive(
  Debug, PartialEq, Eq,
)]
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
  Concat(
    Box<Self>,
    Box<Self>,
  ),
  // Project a product into a sub product
  Project(
    Direction,
    Box<Self>,
  ),
  // Branch on a sum type to two handler functions
  Branch(
    Box<Self>,
    Box<Self>,
  ),
  // Inject a value into a sum type
  Inject(
    Direction,
    Box<Self>,
  ),
}

impl<V> Ast<V> {
  pub fn fun(
    arg: V,
    body: Self,
  ) -> Self {
    Self::Fun(
      arg,
      Box::new(body),
    )
  }

  pub fn app(
    fun: Self,
    arg: Self,
  ) -> Self {
    Self::App(
      Box::new(fun),
      Box::new(arg),
    )
  }

  pub fn label(
    label: impl ToString,
    value: Self,
  ) -> Self {
    Self::Label(
      label.to_string(),
      Box::new(value),
    )
  }

  pub fn unlabel(
    value: Self,
    label: impl ToString,
  ) -> Self {
    Self::Unlabel(
      Box::new(value),
      label.to_string(),
    )
  }

  pub fn project(
    dir: Direction,
    value: Self,
  ) -> Self {
    Self::Project(
      dir,
      Box::new(value),
    )
  }

  pub fn concat(
    left: Self,
    right: Self,
  ) -> Self {
    Self::Concat(
      Box::new(left),
      Box::new(right),
    )
  }

  pub fn inject(
    dir: Direction,
    value: Self,
  ) -> Self {
    Self::Inject(
      dir,
      Box::new(value),
    )
  }

  pub fn branch(
    left: Self,
    right: Self,
  ) -> Self {
    Self::Branch(
      Box::new(left),
      Box::new(right),
    )
  }
}
