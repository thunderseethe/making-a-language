use crate::{Ast, Direction, NodeId, Var, ItemId};

pub fn make_vars<const N: usize>() -> [Var; N] {
  let mut vars = [Var(0); N];
  for (i, var) in vars.iter_mut().enumerate() {
    *var = Var(i);
  }
  vars
}

/// AstBuilder should only be used for testing.
/// It is not thread safe, and just offers convenience for constructing ASTs by hand.
#[derive(Default)]
pub struct AstBuilder {
  node_id: std::cell::Cell<u32>,
}

impl AstBuilder {
  fn next_id(&self) -> NodeId {
    let id = self.node_id.get();
    self.node_id.set(id + 1);
    NodeId(id)
  }

  pub fn var<V>(&self, var: V) -> Ast<V> {
    Ast::Var(self.next_id(), var)
  }

  pub fn int<V>(&self, i: i32) -> Ast<V> {
    Ast::Int(self.next_id(), i)
  }

  pub fn make_funs<const N: usize>(&self, body: impl FnOnce([Var; N]) -> Ast<Var>) -> Ast<Var> {
    let vars = make_vars();
    let body = body(vars);
    self.funs(vars, body)
  }
    
  pub fn funs<V, Vars>(&self, vars: Vars, body: Ast<V>) -> Ast<V> 
  where
    Vars: IntoIterator<Item = V>,
    Vars::IntoIter: DoubleEndedIterator,
  {
    vars.into_iter()
        .rfold(body, |body, var| Ast::fun(self.next_id(), var, body))
  }

  pub fn fun<V>(&self, var: V, body: Ast<V>) -> Ast<V> {
    self.funs([var], body)
  }

  pub fn apps<V>(&self, head: Ast<V>, args: impl IntoIterator<Item = Ast<V>>) -> Ast<V> {
    args.into_iter().fold(head, |head, arg| Ast::app(self.next_id(), head, arg))
  }

  pub fn app<V>(&self, fun: Ast<V>, arg: Ast<V>) -> Ast<V> {
    self.apps(fun, [arg])
  }

  pub fn locals<V, Binds>(&self, binds: Binds, body: Ast<V>) -> Ast<V>
  where
    Binds: IntoIterator<Item = (V, Ast<V>)>,
    Binds::IntoIter: DoubleEndedIterator,
  {
    binds.into_iter().rfold(body, |body, (var, defn)| {
      Ast::app(self.next_id(), Ast::fun(self.next_id(), var, body), defn)
    })
  }

  pub fn label<V>(&self, label: impl ToString, value: Ast<V>) -> Ast<V> {
    Ast::label(self.next_id(), label, value)
  }
  pub fn unlabel<V>(&self, value: Ast<V>, label: impl ToString) -> Ast<V> {
    Ast::unlabel(self.next_id(), value, label)
  }

  pub fn concat<V>(&self, left: Ast<V>, right: Ast<V>) -> Ast<V> {
    Ast::concat(self.next_id(), left, right)
  }

  pub fn project<V>(&self, dir: Direction, value: Ast<V>) -> Ast<V> {
    Ast::project(self.next_id(), dir, value)
  }

  pub fn branch<V>(&self, left: Ast<V>, right: Ast<V>) -> Ast<V> {
    Ast::branch(self.next_id(), left, right)
  }

  pub fn inject<V>(&self, dir: Direction, value: Ast<V>) -> Ast<V> {
    Ast::inject(self.next_id(), dir, value)
  }

  pub fn item<V>(&self, item: ItemId) -> Ast<V> {
    Ast::Item(self.next_id(), item)
  }
}

