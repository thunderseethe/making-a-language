use std::iter::Peekable;
use std::ops::{ControlFlow, Range};

use bit_set::BitSet;
use enum_iterator::{all, Sequence};
use logos::{Logos, SpannedIter};
pub use rowan;
pub use rowan::api::SyntaxNode;
use rowan::{GreenNode, GreenNodeBuilder, SyntaxKind};

pub type Cst = GreenNode;

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

impl Syntax {
  fn raw(&self) -> u16 {
    let kind: SyntaxKind = (*self).into();
    kind.0
  }
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
      .map(|(tok, _)| match tok {
        Ok(tok) => *tok,
        Err(_) => Syntax::Error,
      })
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

  fn at_any(&mut self, recovery_set: &BitSet) -> bool {
    recovery_set.contains(self.peek().raw().into())
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

fn bitset(syntax: impl IntoIterator<Item = Syntax>) -> BitSet {
  let mut bit_set = BitSet::new();
  for syn in syntax {
    let kind: SyntaxKind = syn.into();
    bit_set.insert(kind.0.into());
  }
  bit_set
}

fn unioning(bitset: &BitSet, syntax: impl IntoIterator<Item = Syntax>) -> BitSet {
  let mut bs = bitset.clone();
  bs.extend(syntax.into_iter().map(|s| s.raw().into()));
  bs
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
  in_error: bool,
}

impl<'a> Parser<'a> {
  fn new(content: &'a str) -> Self {
    Self {
      input: Input::new(content),
      builder: GreenNodeBuilder::default(),
      errors: vec![],
      in_error: false,
    }
  }

  fn with<T>(&mut self, node: Syntax, body: impl FnOnce(&mut Self) -> T) -> T {
    self.builder.start_node(node.into());

    let res = body(self);

    self.builder.finish_node();

    res
  }

  fn recover_until(&mut self, anchor: &BitSet, expected: Vec<Syntax>) {
    let mut discard_toks = vec![];
    while !self.input.at_any(anchor) {
      let tok = self.input.peek();
      let Some(span) = self.input.advance() else {
        break;
      };

      discard_toks.push((tok, span));
    }
    // If we're already at an anchor there is nothing to do.
    if discard_toks.is_empty() {
      if !self.in_error {
        self.in_error = true;
        self.errors.push(ParseError {
          expected,
          span: self.input.lexer.peek().map(|(_, span)| span.clone()).unwrap_or_else(|| {
            let len = self.input.content.len();
            len..len
          }),
        });
      }
      return;
    }

    // This is safe because discard_toks is not empty.
    let mut err_span = discard_toks[0].1.clone();
    self.with(Syntax::Error, |this| {
      for (tok, span) in discard_toks {
        err_span.end = span.end;
        this.builder.token(tok.into(), &self.input.content[span]);
      }
    });
    if !self.in_error {
      self.in_error = true;
      self.errors.push(ParseError {
        expected,
        span: err_span,
      });
    }
  }

  fn expect(&mut self, token: Syntax, anchor: &BitSet) -> Option<usize> {
    match self.input.eat(token) {
      Some(str) => {
        self.in_error = false;
        self.builder.token(token.into(), str);
        Some(str.len())
      }
      None => {
        let mut bs = BitSet::new();
        bs.insert(token.raw().into());
        bs.union_with(anchor);
        self.recover_until(&bs, vec![token]);
        // Don't emit an error if we're already at an anchor.
        None
      }
    }
  }

  fn atom(&mut self, anchor: &BitSet) -> ControlFlow<()> {
    // TODO: Figure out where this goes.
    match self.input.peek() {
      Syntax::LeftParen => {
        self.with(Syntax::ParenthesizedExpr, |this| {
          this.expect(Syntax::LeftParen, anchor);
          this.whitespace();
          this.expr(&unioning(anchor, [Syntax::RightParen]));
          this.whitespace();
          this.expect(Syntax::RightParen, anchor);
        });
      }
      Syntax::Backslash => {
        self.with(Syntax::Fun, |this| {
          this.expect(Syntax::Backslash, anchor);
          this.whitespace();
          this.with(Syntax::FunBinder, |this| {
            this.expect(Syntax::Identifier, anchor)
          });
          this.whitespace();
          this.expect(Syntax::Arrow, anchor);
          this.whitespace();
          this.expr(anchor);
          this.whitespace();
        });
      }
      Syntax::Identifier => {
        self.with(Syntax::Var, |this| this.expect(Syntax::Identifier, anchor));
      }
      Syntax::Int => {
        self.with(Syntax::IntegerExpr, |this| this.expect(Syntax::Int, anchor));
      }
      _ => {
        return ControlFlow::Break(());
      }
    };

    ControlFlow::Continue(())
  }

  // A series of applications.
  fn app(&mut self, anchor: &BitSet) {
    self.with(Syntax::App, |this| {
      // An application must have atleast one atom within it
      if let ControlFlow::Break(()) = this.atom(anchor) {
        this.recover_until(
          anchor,
          vec![Syntax::Expr],
        );
        return;
      }
      this.whitespace();

      while let ControlFlow::Continue(()) = this.atom(anchor) {
        this.whitespace();
      }
    })
  }

  fn expr(&mut self, anchor: &BitSet) {
    self.with(Syntax::Expr, |this| {
      this.whitespace();
      while this.input.at(Syntax::LetKw) {
        this.with(Syntax::Let, |this| {
          this.expect(
            Syntax::LetKw,
            &unioning(
              anchor,
              [Syntax::Identifier, Syntax::Equal, Syntax::Semicolon],
            ),
          );
          this.whitespace();
          this.with(Syntax::LetBinder, |this| {
            this.expect(
              Syntax::Identifier,
              &unioning(anchor, [Syntax::Equal, Syntax::Semicolon]),
            )
          });
          this.whitespace();
          this.expect(Syntax::Equal, &unioning(anchor, [Syntax::Semicolon]));
          this.whitespace();
          this.expr(
            &anchor
              .union(&bitset([Syntax::Semicolon, Syntax::LetKw]))
              .collect::<BitSet>(),
          );
          this.whitespace();
          this.expect(Syntax::Semicolon, &unioning(anchor, [Syntax::LetKw]));
          this.whitespace();
        })
      }

      // A series of lets is ended by an application.
      this.app(anchor);
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
      this.expr(&bitset([Syntax::EndOfFile]));
      if !this.input.at(Syntax::EndOfFile) {
        this.recover_until(&BitSet::new(), vec![Syntax::EndOfFile]);
      }
    });
    (self.builder.finish(), self.errors)
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
        Program@0..34
          Expr@0..34
            Whitespaces@0..1 "\n"
            Let@1..24
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..6
                Identifier@5..6 "x"
              Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..20
                App@9..20
                  Fun@9..20
                    Backslash@9..10 "\\"
                    FunBinder@10..11
                      Identifier@10..11 "a"
                    Whitespaces@11..12 " "
                    Arrow@12..14 "->"
                    Whitespaces@14..15 " "
                    Expr@15..20
                      App@15..17
                        Var@15..16
                          Identifier@15..16 "a"
                        Whitespaces@16..17 " "
                      Error@17..20
                        Arrow@17..19 "->"
                        Whitespaces@19..20 "\n"
              Error@20..23 "let"
              Whitespaces@23..24 " "
            App@24..26
              Var@24..25
                Identifier@24..25 "y"
              Whitespaces@25..26 " "
            Error@26..34
              Equal@26..27 "="
              Whitespaces@27..28 " "
              Int@28..29 "3"
              Whitespaces@29..30 "\n"
              Identifier@30..31 "x"
              Whitespaces@31..32 " "
              Identifier@32..33 "y"
              Whitespaces@33..34 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
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
        Program@0..79
          Expr@0..79
            Whitespaces@0..1 "\n"
            Let@1..61
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..10
                Identifier@5..10 "x_y_2"
              Whitespaces@10..11 " "
              Equal@11..12 "="
              Whitespaces@12..13 " "
              Expr@13..59
                App@13..59
                  ParenthesizedExpr@13..36
                    LeftParen@13..14 "("
                    Whitespaces@14..15 " "
                    Expr@15..35
                      App@15..35
                        Fun@15..35
                          Backslash@15..16 "\\"
                          Whitespaces@16..17 " "
                          FunBinder@17..18
                            Identifier@17..18 "x"
                          Whitespaces@18..19 " "
                          Arrow@19..21 "->"
                          Whitespaces@21..27 " \n    "
                          Expr@27..35
                            App@27..35
                              Fun@27..35
                                Backslash@27..28 "\\"
                                Whitespaces@28..29 " "
                                FunBinder@29..30
                                  Identifier@29..30 "y"
                                Whitespaces@30..31 " "
                                Arrow@31..33 "->"
                                Whitespaces@33..34 " "
                                Expr@34..35
                                  App@34..35
                                    Var@34..35
                                      Identifier@34..35 "x"
                    RightParen@35..36 ")"
                  Whitespaces@36..37 " "
                  IntegerExpr@37..38
                    Int@37..38 "2"
                  Whitespaces@38..39 " "
                  ParenthesizedExpr@39..56
                    LeftParen@39..40 "("
                    Expr@40..55
                      App@40..55
                        Fun@40..55
                          Backslash@40..41 "\\"
                          FunBinder@41..42
                            Identifier@41..42 "z"
                          Whitespaces@42..43 " "
                          Error@43..50 "test_id"
                          Whitespaces@50..51 " "
                          Expr@51..55
                            App@51..51
                            Error@51..55
                              Arrow@51..53 "->"
                              Whitespaces@53..54 " "
                              Identifier@54..55 "z"
                    RightParen@55..56 ")"
                  Whitespaces@56..59 "\n  "
              Semicolon@59..60 ";"
              Whitespaces@60..61 "\n"
            App@61..79
              ParenthesizedExpr@61..72
                LeftParen@61..62 "("
                Whitespaces@62..63 " "
                Expr@63..71
                  App@63..71
                    Fun@63..71
                      Backslash@63..64 "\\"
                      Whitespaces@64..65 " "
                      FunBinder@65..66
                        Identifier@65..66 "x"
                      Whitespaces@66..67 " "
                      Arrow@67..69 "->"
                      Whitespaces@69..70 " "
                      Expr@70..71
                        App@70..71
                          Var@70..71
                            Identifier@70..71 "x"
                RightParen@71..72 ")"
              Whitespaces@72..73 " "
              Var@73..78
                Identifier@73..78 "x_y_2"
              Whitespaces@78..79 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_let_in_invalid_position() {
    let input = r#"
let y = \x -> x;
y let a = 1;
y a 
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..36
          Expr@0..36
            Whitespaces@0..1 "\n"
            Let@1..18
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..6
                Identifier@5..6 "y"
              Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..16
                App@9..16
                  Fun@9..16
                    Backslash@9..10 "\\"
                    FunBinder@10..11
                      Identifier@10..11 "x"
                    Whitespaces@11..12 " "
                    Arrow@12..14 "->"
                    Whitespaces@14..15 " "
                    Expr@15..16
                      App@15..16
                        Var@15..16
                          Identifier@15..16 "x"
              Semicolon@16..17 ";"
              Whitespaces@17..18 "\n"
            App@18..20
              Var@18..19
                Identifier@18..19 "y"
              Whitespaces@19..20 " "
            Error@20..36
              LetKw@20..23 "let"
              Whitespaces@23..24 " "
              Identifier@24..25 "a"
              Whitespaces@25..26 " "
              Equal@26..27 "="
              Whitespaces@27..28 " "
              Int@28..29 "1"
              Semicolon@29..30 ";"
              Whitespaces@30..31 "\n"
              Identifier@31..32 "y"
              Whitespaces@32..33 " "
              Identifier@33..34 "a"
              Whitespaces@34..36 " \n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_recovers_from_missing_semi() {
    let input = r#"
let a = (\x -> x)
let b = 3;
a b
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..34
          Expr@0..31
            Whitespaces@0..1 "\n"
            Let@1..19
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..6
                Identifier@5..6 "a"
              Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..18
                App@9..18
                  ParenthesizedExpr@9..18
                    LeftParen@9..10 "("
                    Expr@10..17
                      App@10..17
                        Fun@10..17
                          Backslash@10..11 "\\"
                          FunBinder@11..12
                            Identifier@11..12 "x"
                          Whitespaces@12..13 " "
                          Arrow@13..15 "->"
                          Whitespaces@15..16 " "
                          Expr@16..17
                            App@16..17
                              Var@16..17
                                Identifier@16..17 "x"
                    RightParen@17..18 ")"
              Whitespaces@18..19 "\n"
            Let@19..30
              LetKw@19..22 "let"
              Whitespaces@22..23 " "
              LetBinder@23..24
                Identifier@23..24 "b"
              Whitespaces@24..25 " "
              Equal@25..26 "="
              Whitespaces@26..27 " "
              Expr@27..28
                App@27..28
                  IntegerExpr@27..28
                    Int@27..28 "3"
              Semicolon@28..29 ";"
              Whitespaces@29..30 "\n"
            App@30..31
              Var@30..31
                Identifier@30..31 "a"
          Error@31..34
            Whitespaces@31..32 " "
            Identifier@32..33 "b"
            Whitespaces@33..34 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_test_missing_expr_after_let() {
    let input = r#"
let a = (\x -> x);
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..20
          Expr@0..20
            Whitespaces@0..1 "\n"
            Let@1..20
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..6
                Identifier@5..6 "a"
              Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..18
                App@9..18
                  ParenthesizedExpr@9..18
                    LeftParen@9..10 "("
                    Expr@10..17
                      App@10..17
                        Fun@10..17
                          Backslash@10..11 "\\"
                          FunBinder@11..12
                            Identifier@11..12 "x"
                          Whitespaces@12..13 " "
                          Arrow@13..15 "->"
                          Whitespaces@15..16 " "
                          Expr@16..17
                            App@16..17
                              Var@16..17
                                Identifier@16..17 "x"
                    RightParen@17..18 ")"
              Semicolon@18..19 ";"
              Whitespaces@19..20 "\n"
            App@20..20
              Error@20..20
                EndOfFile@20..20 ""
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_test_missing_expr_within_parens() {
    let input = "() b";
    let (tree, errors) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..4
          Expr@0..4
            App@0..4
              ParenthesizedExpr@0..2
                LeftParen@0..1 "("
                Expr@1..1
                  App@1..1
                RightParen@1..2 ")"
              Whitespaces@2..3 " "
              Var@3..4
                Identifier@3..4 "b"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));

    let expect_errors = expect_test::expect!["[ParseError { expected: [Expr], span: 1..2 }]"];
    expect_errors.assert_eq(&format!("{:?}", errors));
  }
}
