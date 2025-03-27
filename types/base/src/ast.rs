use crate::{Ast, Var};

pub fn make_vars<const N: usize>() -> [Var; N] {
  let mut vars = [Var(0); N];
  for (i, var) in vars.iter_mut().enumerate() {
    *var = Var(i);
  }
  vars
}

impl<V> Ast<V> {
  /// Shorthand to construct a function of multiple parameters.
  pub fn funs<Vars>(vars: Vars, body: Self) -> Self
  where
    Vars: IntoIterator<Item = V>,
    Vars::IntoIter: DoubleEndedIterator,
  {
    vars
      .into_iter()
      .rfold(body, |body, var| Ast::fun(var, body))
  }

  /// Shorthand to construct a series of applications.
  pub fn apps(head: Self, args: impl IntoIterator<Item = Self>) -> Self {
    args.into_iter().fold(head, |head, arg| Ast::app(head, arg))
  }

  /// Shorthand to construct a series of locally bound variables.
  /// Our AST doesn't support locals explicitly but we can represent a local `let var = defn; body`
  /// as `Ast::app(Ast::fun(var, body), defn)`.
  pub fn locals<Binds>(binds: Binds, body: Self) -> Self
  where
    Binds: IntoIterator<Item = (V, Self)>,
    Binds::IntoIter: DoubleEndedIterator,
  {
    binds.into_iter().rfold(body, |body, (var, defn)| {
      Ast::app(Ast::fun(var, body), defn)
    })
  }
}
