use std::fmt::Debug;
use std::ops::Range;

use parser_base::{Node, Syntax, Token};
use syntree::{FlavorDefault, Tree};
use types_base::Ast;

#[derive(Debug, PartialEq, Eq)]
pub enum ErrorKind {
  MissingNode(Node),
  MissingToken(Token),
  ProgramMissingExpr,
  ExpectedLetOrAppInExpr(Syntax),
  LetMissingBinding,
  LetMissingExpr,
  Unexpected(Vec<Syntax>),
  InvalidInt(std::num::ParseIntError),
  FunMissingIdentifier,
  FunMissingExpr,
  EmptyApplication,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DesugarError {
  kind: ErrorKind,
  span: Range<usize>,
}

impl DesugarError {
  fn new(kind: ErrorKind, span: Range<usize>) -> Self {
    Self { kind, span }
  }
}

type ParseNode<'a> = syntree::Node<'a, Syntax, FlavorDefault>;

struct Desugar<'a> {
  source: &'a str,
}

impl<'a> Desugar<'a> {
  fn new(source: &'a str) -> Self {
    Self { source }
  }

  fn desugar_program(
    &mut self,
    cst: Tree<Syntax, FlavorDefault>,
  ) -> Result<Ast<String>, DesugarError> {
    let node = cst
      .first()
      .filter(|node| node.value() == Syntax::Node(Node::Program))
      .ok_or(DesugarError::new(
        ErrorKind::ProgramMissingExpr,
        cst.range(),
      ))?;

    let Some(expr) = node.first() else {
      return Err(DesugarError::new(
        ErrorKind::ProgramMissingExpr,
        cst.range(),
      ));
    };

    self.desugar_expr(expr)
  }

  fn desugar_expr(&mut self, expr: ParseNode<'_>) -> Result<Ast<String>, DesugarError> {
    if expr.value() != Syntax::Node(Node::Lets) {
      return Err(DesugarError::new(
        ErrorKind::MissingNode(Node::Lets),
        expr.range(),
      ));
    }

    let mut binds = vec![];
    // The only tokens that appear in Lets are whitespace that we are happy to skip here.
    for child in expr.children().skip_tokens() {
      if child.value() == Syntax::Node(Node::Let) {
        let binding = self.desugar_let(child)?;
        binds.push(binding)
      } else if child.value() == Syntax::Node(Node::App) {
        let app = self.desugar_app_spine(child)?;
        return Ok(
          binds
            .into_iter()
            .rfold(app, |body, (var, arg)| Ast::app(Ast::fun(var, body), arg)),
        );
      } else {
        return Err(DesugarError::new(
          ErrorKind::ExpectedLetOrAppInExpr(child.value()),
          child.range(),
        ));
      }
    }

    Err(DesugarError::new(
      ErrorKind::MissingNode(Node::App),
      expr.last().unwrap_or(expr).range(),
    ))
  }

  fn desugar_let(&mut self, bind: ParseNode<'_>) -> Result<(String, Ast<String>), DesugarError> {
    let mut children = bind.children();

    expect_token(&mut children, Token::LetKw)?;

    let Some(var) =
      skip_whitespace(&mut children).filter(|id| id.value() == Syntax::Token(Token::Identifier))
    else {
      return Err(DesugarError::new(
        ErrorKind::LetMissingBinding,
        bind.range(),
      ));
    };

    expect_token(&mut children, Token::Equal)?;

    let Some(expr) = skip_whitespace(&mut children) else {
      return Err(DesugarError::new(ErrorKind::LetMissingExpr, bind.range()));
    };

    let ast = self.desugar_expr(expr)?;

    expect_token(&mut children, Token::Semicolon)?;

    // Skip any trailing whitespace
    skip_whitespace(&mut children);

    let extra = children.map(|node| node.value()).collect::<Vec<_>>();
    if !extra.is_empty() {
      return Err(DesugarError::new(
        ErrorKind::Unexpected(extra),
        bind.range(),
      ));
    }

    Ok((self.source[var.range()].to_string(), ast))
  }

  fn desugar_app_spine(&mut self, app: ParseNode<'_>) -> Result<Ast<String>, DesugarError> {
    let mut children = app.children();

    let mut spine = vec![];
    while let Some(atom) = skip_whitespace(&mut children) {
      let expr = match atom.value() {
        Syntax::Node(Node::Fun) => self.desugar_fun(atom)?,
        Syntax::Node(Node::ParenthesizedExpr) => self.desugar_paren_expr(atom)?,
        Syntax::Node(Node::Var) => {
          let var = atom
            .first()
            .filter(|tok| tok.value() == Syntax::Token(Token::Identifier))
            .expect("Var parse node should always be constructed with identifier as it's child");
          Ast::Var(self.source[var.range()].to_string())
        }
        Syntax::Token(Token::Int) => self.source[atom.range()]
          .parse()
          .map(Ast::Int)
          .map_err(|err| DesugarError::new(ErrorKind::InvalidInt(err), atom.range()))?,
        _ => {
          let mut extra = vec![atom.value()];
          extra.extend(children.map(|tok| tok.value()));
          return Err(DesugarError::new(ErrorKind::Unexpected(extra), app.range()));
        }
      };
      spine.push(expr);
    }

    spine
      .into_iter()
      .reduce(Ast::app)
      .ok_or(DesugarError::new(ErrorKind::EmptyApplication, app.range()))
  }

  fn desugar_fun(&mut self, expr: ParseNode<'_>) -> Result<Ast<String>, DesugarError> {
    let mut children = expr.children();
    expect_token(&mut children, Token::Backslash)?;

    let Some(var) =
      skip_whitespace(&mut children).filter(|tok| tok.value() == Syntax::Token(Token::Identifier))
    else {
      return Err(DesugarError::new(
        ErrorKind::FunMissingIdentifier,
        expr.range(),
      ));
    };

    expect_token(&mut children, Token::Arrow)?;

    let Some(body) = skip_whitespace(&mut children) else {
      return Err(DesugarError::new(ErrorKind::FunMissingExpr, expr.range()));
    };

    let body = self.desugar_expr(body)?;

    Ok(Ast::fun(self.source[var.range()].to_string(), body))
  }

  fn desugar_paren_expr(&mut self, expr: ParseNode<'_>) -> Result<Ast<String>, DesugarError> {
    let mut children = expr.children();
    expect_token(&mut children, Token::LeftParen)?;

    let Some(expr) = skip_whitespace(&mut children) else {
      return Err(DesugarError::new(
        ErrorKind::MissingNode(Node::Lets),
        expr.range(),
      ));
    };
    let expr = self.desugar_expr(expr)?;

    expect_token(&mut children, Token::RightParen)?;
    Ok(expr)
  }
}

fn expect_token(
  children: &mut syntree::node::Children<'_, Syntax, FlavorDefault>,
  token: Token,
) -> Result<(), DesugarError> {
  // TODO: Figure out how to give this a meaningful span.
  let tok =
    skip_whitespace(children).ok_or(DesugarError::new(ErrorKind::MissingToken(token), 0..1))?;

  if tok.value() == Syntax::Token(token) {
    Ok(())
  } else {
    Err(DesugarError::new(
      ErrorKind::MissingToken(token),
      tok.range(),
    ))
  }
}

fn skip_whitespace<'a>(
  children: &mut impl Iterator<Item = syntree::Node<'a, Syntax, FlavorDefault>>,
) -> Option<syntree::Node<'a, Syntax, FlavorDefault>> {
  let possibly_whitespace = children.next()?;
  if possibly_whitespace.value() == Syntax::Token(Token::Whitespaces) {
    return children.next();
  }
  Some(possibly_whitespace)
}

// TODO: Combine content and tree into one output of parsing.
// Possibly with an API
pub fn desugar(
  source: &str,
  cst: Tree<Syntax, FlavorDefault>,
) -> Result<Ast<String>, DesugarError> {
  Desugar::new(source).desugar_program(cst)
}

#[cfg(test)]
mod tests {

  use super::*;

  fn desugar(input: &str) -> Result<Ast<String>, DesugarError> {
    let cst = parser_base::parse(input);
    let mut o = vec![];
    syntree::print::print_with_source(&mut o, &cst, input).unwrap();
    println!("{}", String::from_utf8(o).unwrap());
    crate::desugar(input, cst)
  }

  #[test]
  fn it_works() {
    let input = r#"
let x = \a -> a;
let y = \ 
  b -> x b;
y (
  \c -> c
   )
4
"#;

    let ast = desugar(input);

    let ast = match ast {
      Ok(ast) => ast,
      Err(err) => {
        println!("{:?}", err);
        panic!("{}", &input[err.span])
      }
    };

    assert_eq!(
      ast,
      Ast::app(
        Ast::fun(
          "x".to_string(),
          Ast::app(
            Ast::fun(
              "y".to_string(),
              Ast::app(
                Ast::app(
                  Ast::Var("y".to_string()),
                  Ast::fun("c".to_string(), Ast::Var("c".to_string()))
                ),
                Ast::Int(4)
              )
            ),
            Ast::fun(
              "b".to_string(),
              Ast::app(Ast::Var("x".to_string()), Ast::Var("b".to_string()))
            )
          )
        ),
        Ast::fun("a".to_string(), Ast::Var("a".to_string()))
      )
    );
  }
}
