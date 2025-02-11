use pretty::{DocAllocator, DocBuilder, Pretty};

use crate::{Row, TyApp};

use super::{Kind, Type, TypeVar, Var, VarId, IR};

impl<'a, D, A> Pretty<'a, D, A> for VarId
where
  A: 'a,
  D: DocAllocator<'a, A>,
{
  fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, A> {
    allocator.text("V").append(allocator.as_string(self.0))
  }
}

impl<'a, D, A> Pretty<'a, D, A> for Var
where
  A: 'a,
  D: DocAllocator<'a, A>,
{
  fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, A> {
    self.id.pretty(allocator)
  }
}

impl<'a, D, A> Pretty<'a, D, A> for TypeVar
where
  A: 'a,
  D: DocAllocator<'a, A>,
{
  fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, A> {
    allocator.text("T").append(allocator.as_string(self.0))
  }
}

impl Type {
  fn collect_fun_tys_into(self, args: &mut Vec<Type>) {
    if let Type::Fun(arg, ret) = self {
      args.push(*arg);
      ret.collect_fun_tys_into(args)
    } else {
      args.push(self);
    }
  }

  fn collect_forall_kinds(self, expected_kind: Kind, kinds: &mut Vec<Kind>) -> Type {
    match self {
      Type::TyFun(kind, ty) if kind == expected_kind => {
        kinds.push(kind);
        ty.collect_forall_kinds(expected_kind, kinds)
      }
      ty => ty,
    }
  }
}

impl<'a, D, A> Pretty<'a, D, A> for Kind
where
  A: 'a,
  D: DocAllocator<'a, A>,
{
  fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
    match self {
      Kind::Type => allocator.text("Type"),
      Kind::Row => allocator.text("Row"),
    }
  }
}

impl<'a, D> Pretty<'a, D> for Row
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D, ()> {
    match self {
      Row::Open(var) => var.pretty(a),
      Row::Closed(tys) => {
        let single = a.intersperse(
          tys.clone().into_iter().map(|ty| ty.pretty(a)),
          a.text(",").append(a.space()),
        );
        let multi = a
          .space()
          .append(a.intersperse(
            tys.into_iter().map(|ty| ty.pretty(a)),
            a.hardline().append(a.text(", ")),
          ))
          .append(a.hardline())
          .align();
        multi.flat_alt(single).group()
      }
    }
  }
}

impl<'a, D> Pretty<'a, D> for Type
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    match self {
      Type::Int => a.text("Int"),
      Type::Var(type_var) => type_var.pretty(a),
      Type::Fun(arg, ret) => {
        let mut tys = vec![*arg];
        ret.collect_fun_tys_into(&mut tys);
        a.intersperse(tys.into_iter().map(|ty| ty.pretty(a)), " -> ")
      }
      Type::TyFun(kind, ty) => {
        let mut kinds = vec![kind];
        let ty = ty.collect_forall_kinds(kind, &mut kinds);
        a.text("forall")
          .append(a.space())
          .append(
            a.intersperse(
              kinds.into_iter().map(|kind| kind.pretty(a)),
              a.text(",").append(a.space()),
            )
            .brackets(),
          )
          .append(a.space())
          .append(".")
          .append(a.line().append(ty.pretty(a).group()).nest(2))
      }
      Type::Prod(row) => row.pretty(a).braces(),
      Type::Sum(row) => row.pretty(a).angles(),
    }
  }
}

impl<'a, D> Pretty<'a, D> for TyApp
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> DocBuilder<'a, D, ()> {
    match self {
      TyApp::Ty(ty) => a.text("Ty").append(ty.pretty(a).parens()),
      TyApp::Row(row) => a.text("Row").append(row.pretty(a).parens()),
    }
  }
}

impl IR {
  fn collect_fun_vars(self, vars: &mut Vec<Var>) -> IR {
    if let IR::Fun(var, body) = self {
      vars.push(var);
      body.collect_fun_vars(vars)
    } else {
      self
    }
  }

  fn collect_app_args(self, args: &mut Vec<IR>) -> IR {
    if let IR::App(fun, arg) = self {
      args.push(*arg);
      fun.collect_app_args(args)
    } else {
      args.reverse();
      self
    }
  }

  fn collect_tyfun_kinds(self, expected_kind: Kind, kinds: &mut Vec<Kind>) -> IR {
    match self {
      IR::TyFun(kind, body) if kind == expected_kind => {
        kinds.push(kind);
        body.collect_tyfun_kinds(expected_kind, kinds)
      }
      ir => ir,
    }
  }

  fn collect_tyapp_tys(self, tys: &mut Vec<TyApp>) -> IR {
    if let IR::TyApp(body, ty) = self {
      tys.push(ty);
      body.collect_tyapp_tys(tys)
    } else {
      tys.reverse();
      self
    }
  }

  fn collect_locals(self, locals: &mut Vec<(Var, Box<Self>)>) -> Self {
    if let IR::Local(var, defn, body) = self {
      locals.push((var, defn));
      body.collect_locals(locals)
    } else {
      self
    }
  }
}

impl<'a, D> Pretty<'a, D> for IR
where
  D: DocAllocator<'a>,
  DocBuilder<'a, D>: Clone + 'a,
{
  fn pretty(self, a: &'a D) -> pretty::DocBuilder<'a, D> {
    match self {
      IR::Var(var) => var.pretty(a),
      IR::Int(i) => a.as_string(i),
      IR::Fun(var, body) => {
        let mut vars = vec![var.clone()];
        let ir = body.collect_fun_vars(&mut vars);
        a.text("fun")
          .append(a.space())
          .append(
            a.intersperse(
              vars.into_iter().map(|var| var.pretty(a)),
              a.line_().append(",").append(a.space()),
            )
            .brackets()
            .group(),
          )
          .append(a.line().append(ir.pretty(a)).nest(2))
          .parens()
      }
      IR::App(fun, arg) => {
        let mut args = vec![*arg];
        let fun = fun.collect_app_args(&mut args);
        fun
          .pretty(a)
          .append(
            a.line()
              .append(a.intersperse(args.into_iter().map(|ir| ir.pretty(a)), " "))
              .nest(2),
          )
          .parens()
          .group()
      }
      IR::TyFun(kind, ir) => {
        let mut kinds = vec![kind];
        let ir = ir.collect_tyfun_kinds(kind, &mut kinds);
        a.text("ty_fun")
          .append(a.space())
          .append(
            a.intersperse(kinds.into_iter().map(|kind| kind.pretty(a)), " ")
              .brackets(),
          )
          .append(a.line().append(ir.pretty(a)).nest(2))
          .parens()
      }
      IR::TyApp(ty_fun, ty) => {
        let mut tys = vec![ty];
        let ir = ty_fun.collect_tyapp_tys(&mut tys);
        a.text("ty_app")
          .append(a.space())
          .append(ir.pretty(a).brackets())
          .append(a.line().append(a.intersperse(tys, a.space())).nest(2))
          .parens()
          .group()
      }
      IR::Local(var, defn, body) => {
        let mut locals = vec![(var, defn)];
        let body = body.collect_locals(&mut locals);

        let pretty_local = |(var, defn): (Var, Box<IR>)| {
          var
            .pretty(a)
            .append(a.space())
            .append(defn.pretty(a))
            .parens()
        };
        let single = a
          .intersperse(
            locals.clone().into_iter().map(pretty_local),
            a.text(",").append(a.space()),
          )
          .brackets()
          .group();
        let multi = a.hardline().append(
          a.space()
            .append(a.intersperse(
              locals.into_iter().map(pretty_local),
              a.hardline().append(a.text(",")).append(a.space()),
            ))
            .append(a.hardline())
            .brackets()
            .align(),
        ).nest(2);

        a.text("let")
          .append(multi.flat_alt(single))
          .append(a.line().append(body.pretty(a)).nest(2))
          .parens()
          .group()
      }
      IR::Tuple(elems) => {
        let single = a
          .intersperse(
            elems.clone().into_iter().map(|ir| ir.pretty(a)),
            a.text(",").append(a.space()),
          )
          .braces();
        let multi = a
          .space()
          .append(a.intersperse(
            elems.into_iter().map(|ir| ir.pretty(a)),
            a.hardline().append(a.text(", ")),
          ))
          .append(a.hardline())
          .braces()
          .align();
        multi.flat_alt(single).group()
      }
      IR::Field(ir, field) => ir.pretty(a).append(a.as_string(field).brackets()),
      IR::Tag(_, tag, ir) => a
        .as_string(tag)
        .append(":")
        .append(a.space())
        .append(ir.pretty(a))
        .angles(),
      IR::Case(_, ir, branches) => a
        .text("case")
        .append(a.space())
        .append(ir.pretty(a).brackets())
        .append(a.space())
        .append(
          a.hardline()
            .append(a.intersperse(
              branches.into_iter().map(|branch| {
                branch
                  .param
                  .pretty(a)
                  .append(a.space())
                  .append("=>")
                  .append(a.softline().append(branch.body.pretty(a)).nest(2))
              }),
              a.line(),
            ))
            .append(a.line())
            .brackets()
            .nest(2),
        )
        .parens(),
    }
  }
}
