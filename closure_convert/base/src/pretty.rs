use pretty::{DocAllocator, DocBuilder, Pretty};

use crate::{Anf, Atom, Definition, DefinitionId, Locals, Type, Var};

impl<'a, D> Pretty<'a, D> for Atom
where
  D: DocAllocator<'a>,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    match self {
      Atom::Var(var) => var.pretty(a),
      Atom::Int(i) => a.as_string(i),
    }
  }
}

impl<'a, D> Pretty<'a, D> for DefinitionId
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
      Type::I32 => a.text("i32"),
      Type::Closure(arg, ret) => arg
        .pretty(a)
        .append(a.space())
        .append("->")
        .append(a.line().append(ret.pretty(a)).nest(2).group())
        .enclose("〚", "〛"),
      Type::Struct(tys) => a.intersperse(
        tys.into_iter().map(|ty| ty.pretty(a)),
        a.text(",").append(a.space()),
      ).braces().group(),
    }
  }
}

impl<'a, D> Pretty<'a, D> for Anf
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    match self {
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
    }
  }
}

impl<'a, D> Pretty<'a, D> for Locals
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D, ()> {
    a.concat(self.binds.into_iter().map(|(var, exp)| {
        var.clone()
          .pretty(a)
          .append(":")
          .append(a.space())
          .append(var.ty.pretty(a))
          .append(a.space())
          .append(a.text("="))
          .append(a.space())
          .append(exp.pretty(a))
          .append(a.text(";"))
          .append(a.hardline())
    }))
    .append(self.body.pretty(a))
  }
}

impl<'a, D> Pretty<'a, D> for Definition
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D> {
    a.text("defn")
      .append(
        a.intersperse(self.params.into_iter().map(|var| var.clone().pretty(a).append(":").append(var.ty.pretty(a))), ", ")
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
