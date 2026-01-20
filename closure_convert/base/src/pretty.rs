use pretty::{DocAllocator, DocBuilder, Pretty};

use crate::{IR, Item, ItemId, Type, Var};

impl<'a, D> Pretty<'a, D> for ItemId
where
  D: DocAllocator<'a>,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    a.text("item").append(a.as_string(self.0))
  }
}

impl<'a, D> Pretty<'a, D> for Var
where
  D: DocAllocator<'a>,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    a.text("V").append(a.as_string(self.id.0))
  }
}

impl<'a, D> Pretty<'a, D> for Type
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D, ()> {
    match self {
      Type::Int => a.text("i32"),
      Type::Closure(arg, ret) => arg
        .pretty(a)
        .append(a.space())
        .append("->")
        .append(a.line().append(ret.pretty(a)).nest(2).group())
        .brackets(),
      Type::ClosureEnv(closure, env) => a
        .space()
        .append(a.text("code:"))
        .append(a.line().append(closure.pretty(a)).nest(2).group())
        .append(a.line())
        .append(
          a.text(", env: ").append(
            a.intersperse(
              env.into_iter().map(|ty| ty.pretty(a)),
              a.text(",").append(a.space()),
            )
            .braces()
            .nest(2)
            .group(),
          ),
        )
        .append(a.line())
        .braces()
        .align(),
    }
  }
}

impl<'a, D> Pretty<'a, D> for IR
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    /*match self {
      Anf::Atom(atom) => atom.pretty(a),
      Anf::Closure(definition_id, vars) => a
        .text("closure")
        .append(a.space())
        .append(definition_id.pretty(a))
        .append(
          a.line()
            .append(
              a.intersperse(vars.into_iter().map(|var| var.pretty(a)), ", ")
                .brackets(),
            )
            .nest(2)
            .group(),
        )
        .parens(),
      Anf::Apply(head, arg) => a
        .text("apply")
        .append(a.space())
        .append(head.pretty(a))
        .append(a.space())
        .append(arg.pretty(a))
        .parens(),
      Anf::Access(var, field) => var.pretty(a).append(a.as_string(field).brackets()),
    }*/
    match self {
      IR::Var(var) => var.pretty(a),
      IR::Int(i) => a.as_string(i),
      IR::Closure(_, item_id, vars) => a
        .text("closure")
        .append(a.space())
        .append(item_id.pretty(a))
        .append(
          a.line()
            .append(
              a.intersperse(vars.into_iter().map(|var| var.pretty(a)), ", ")
                .brackets(),
            )
            .nest(2)
            .group(),
        )
        .parens(),
      IR::Apply(fun, arg) => a
        .text("apply")
        .append(a.line().append(fun.pretty(a)).nest(2).group())
        .append(a.line().append(arg.pretty(a)).nest(2).group())
        .parens(),
      IR::Local(var, defn, body) => a
        .text("let")
        .append(a.space())
        .append(
          var
            .pretty(a)
            .append(a.line().append(defn.pretty(a)).nest(2).group())
            .parens(),
        )
        .append(a.line().append(body.pretty(a)).nest(2).group())
        .parens(),
      IR::Access(strukt, field) => strukt.pretty(a).append(a.as_string(field).brackets()),
    }
  }
}

impl<'a, D> Pretty<'a, D> for Item
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D> {
    a.text("func")
      .append(
        a.intersperse(
          self
            .params
            .into_iter()
            .map(|var| var.clone().pretty(a).append(":").append(var.ty.pretty(a))),
          ", ",
        )
        .parens(),
      )
      .append(a.space())
      .append(
        a.line()
          .append(self.body.pretty(a))
          .nest(2)
          .append(a.line())
          .braces(),
      )
  }
}
