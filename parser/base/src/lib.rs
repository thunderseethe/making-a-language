use std::hash::Hash;
use std::iter::Peekable;
use std::ops::{ControlFlow, Range};

use enum_iterator::{all, Sequence};
use logos::{Logos, SpannedIter};
pub use rowan::api::SyntaxNode;
pub use rowan;
use rowan::{GreenNode, GreenNodeBuilder, SyntaxKind};
use syntree::flavor;
pub use syntree::{Builder, FlavorDefault, Node as ParseNode, Tree};

pub type Cst = Tree<Syntax, Flavor>;
pub type CstPointer = <Flavor as syntree::Flavor>::Pointer;
pub type RowanCst = GreenNode;

flavor! {
  pub struct Flavor {
    type Index = u32;
    type Width = usize;
  }
}
impl Clone for Flavor {
  fn clone(&self) -> Self {
    Self
  }
}

#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Sequence)]
#[repr(u16)]
pub enum Syntax {
  // Tokens
  #[token("(")]
  LeftParen = 0,
  #[token(")")]
  RightParen,
  #[token("\\")]
  Backslash,
  #[token("=")]
  Equal,
  #[token("->")]
  Arrow,
  #[token("let")]
  LetKw,
  #[token(";")]
  Semicolon,
  #[regex("[\\p{alpha}_]\\w*")]
  Identifier,
  #[regex("\\d+")]
  Int,
  #[regex("\\s+")]
  Whitespaces,
  #[end]
  EndOfFile,
  // Error node
  Error,
  // Nodes
  Fun,
  FunBinder,
  App,
  ParenthesizedExpr,
  Var,
  Let,
  LetBinder,
  Expr,
  IntegerExpr,
  Program,
}

pub fn all_syntax() -> impl Iterator<Item = Syntax> {
  all::<Syntax>()
}

struct Input<'a> {
  content: &'a str,
  lexer: Peekable<SpannedIter<'a, Syntax>>,
}

impl<'a> Input<'a> {
  fn new(content: &'a str) -> Self {
    Self {
      content,
      lexer: Syntax::lexer(content).spanned().peekable(),
    }
  }

  fn peek(&mut self) -> Syntax {
    self
      .lexer
      .peek()
      .map(|(tok, span)| match tok {
        Ok(tok) => tok,
        Err(_) => panic!("{}", &self.content[span.start..span.end]),
      })
      .copied()
      .unwrap_or(Syntax::EndOfFile)
  }

  fn at(&mut self, token: Syntax) -> bool {
    self.peek() == token
  }

  fn advance(&mut self) -> Option<Range<usize>> {
    let (_, span) = self.lexer.next()?;
    Some(span)
  }

  fn eat(&mut self, token: Syntax) -> Option<&str> {
    if self.at(token) {
      self.advance().map(|span| &self.content[span])
    } else {
      None
    }
  }
}

impl From<Syntax> for rowan::SyntaxKind {
  fn from(val: Syntax) -> Self {
    SyntaxKind(val as u16)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}
impl rowan::Language for Lang {
  type Kind = Syntax;

  fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
    unsafe { std::mem::transmute::<u16, Syntax>(raw.0) }
  }

  fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
    kind.into()
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
  pub expected: Vec<Syntax>, 
  pub span: Range<usize>,
}

struct Parser<'a> {
  input: Input<'a>,
  builder: GreenNodeBuilder<'static>,
  errors: Vec<ParseError>,
}

impl<'a> Parser<'a> {
  fn new(content: &'a str) -> Self {
    Self {
      input: Input::new(content),
      builder: GreenNodeBuilder::default(),
      errors: vec![],
    }
  }

  fn with<T>(&mut self, node: Syntax, body: impl FnOnce(&mut Self) -> T) -> T {
    self.builder.start_node(node.into());

    let res = body(self);

    self.builder.finish_node();

    res
  }

  fn expect(&mut self, token: Syntax) -> Option<usize> {
    match self.input.eat(token) {
      Some(str) => {
        self.builder.token(token.into(), str);
        Some(str.len())
      }
      None => {
        if let Some(span) = self.input.advance() {
          self.builder.token(Syntax::Error.into(), &self.input.content[span.clone()]);
          self.errors.push(ParseError { expected: vec![token], span })
        }
        None
      }
    }
  }

  fn atom(&mut self) -> ControlFlow<()> {
    match self.input.peek() {
      Syntax::LeftParen => {
        self.with(Syntax::ParenthesizedExpr, |this| {
          this.expect(Syntax::LeftParen);
          this.whitespace();
          this.expr();
          this.whitespace();
          this.expect(Syntax::RightParen);
        });
      }
      Syntax::Backslash => {
        self.with(Syntax::Fun, |this| {
          this.expect(Syntax::Backslash);
          this.whitespace();
          this.with(Syntax::FunBinder, |this| this.expect(Syntax::Identifier));
          this.whitespace();
          this.expect(Syntax::Arrow);
          this.whitespace();
          this.expr();
          this.whitespace();
        });
      }
      Syntax::Identifier => {
        self.with(Syntax::Var, |this| this.expect(Syntax::Identifier));
      }
      Syntax::Int => {
        self.with(Syntax::IntegerExpr, |this| this.expect(Syntax::Int));
      }
      _ => {
        return ControlFlow::Break(());
      }
    };

    ControlFlow::Continue(())
  }

  // A series of applications.
  fn app(&mut self) {
    self.with(Syntax::App, |this| {
      while let ControlFlow::Continue(()) = this.atom() {
        this.whitespace();
      }
    })
  }

  fn expr(&mut self) {
    self.with(Syntax::Expr, |this| {
      this.whitespace();
      while this.input.at(Syntax::LetKw) {
        this.with(Syntax::Let, |this| {
          this.expect(Syntax::LetKw);
          this.whitespace();
          this.with(Syntax::LetBinder, |this| this.expect(Syntax::Identifier));
          this.whitespace();
          this.expect(Syntax::Equal);
          this.whitespace();
          this.expr();
          this.whitespace();
          this.expect(Syntax::Semicolon);
          this.whitespace();
        })
      }

      // A series of lets is ended by an application.
      this.app();
    })
  }

  fn whitespace(&mut self) {
    if self.input.at(Syntax::Whitespaces) {
      if let Some(span) = self.input.advance() {
        self
          .builder
          .token(Syntax::Whitespaces.into(), &self.input.content[span]);
      }
    }
  }

  fn parse(mut self) -> (GreenNode, Vec<ParseError>) {
    self.with(Syntax::Program, |this| {
      this.expr();
    });
    ( self.builder.finish()
    , self.errors
    )
  }
}

pub fn parse(input: &str) -> (GreenNode, Vec<ParseError>) {
  Parser::new(input).parse()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parsing_multiple_lets_and_multiple_apps() {
    let input = r#"
let x = \a -> a;
let y = \ 
  b -> x b;
y (
  \c -> c
   ) 
4
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"

        let x = \a -> a;
        let y = \ 
          b -> x b;
        y (
          \c -> c
           ) 
        4
    "#]];
    expect.assert_eq(&tree.to_string());
  }

  #[test]
  fn parse_invalid_let() {
    let input = r#"
let x = \a -> a ->
let y = 3
x y
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"

        let x = \a -> a ->
        let y = 3
        x y
    "#]];
    expect.assert_eq(&tree.to_string());
  }

  #[test]
  fn parse_invalid() {
    let input = r#"
let x_y_2 = ( \ x -> 
    \ y -> x) 2 (\z test_id -> z)
  ;
( \ x -> x) x_y_2
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"

        let x_y_2 = ( \ x -> 
            \ y -> x) 2 (\z test_id -> z)
  "#]];
    expect.assert_eq(&tree.to_string());
  }
}
