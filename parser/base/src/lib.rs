use std::iter::Peekable;
use std::ops::{ControlFlow, Range};

use enum_iterator::{Sequence, all};
use im::{HashSet, hashset};
use logos::Logos;
pub use rowan;
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
  #[token("|")]
  VerticalBar,
  #[token("=")]
  Equal,
  #[token(";")]
  Semicolon,
  #[token("let")]
  LetKw,
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
  lexer: Peekable<logos::SpannedIter<'a, Syntax>>,
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

  fn at_any(&mut self, recovery_set: HashSet<Syntax>) -> bool {
    recovery_set.contains(&self.peek())
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

fn unioning(orig: &HashSet<Syntax>, syntax: impl IntoIterator<Item = Syntax>) -> HashSet<Syntax> {
  let mut set = orig.clone();
  set.extend(syntax);
  set
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

  fn recover_until(&mut self, anchor: HashSet<Syntax>, expected: Vec<Syntax>) {
    let mut discard_toks = vec![];
    while !self.input.at_any(anchor.clone()) {
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
          span: self
            .input
            .lexer
            .peek()
            .map(|(_, span)| span.clone())
            .unwrap_or_else(|| {
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

  fn ate(&mut self, token: Syntax) -> ControlFlow<()> {
    let Some(str) = self.input.eat(token) else {
      // We didn't consume the right token so continue.
      return ControlFlow::Continue(());
    };
    self.in_error = false;
    self.builder.token(token.into(), str);
    self.whitespace();
    // We consumed the expected token, so we break to return early.
    ControlFlow::Break(())
  }

  fn expect(&mut self, token: Syntax, mut anchor_set: HashSet<Syntax>) {
    // Happy path
    if let ControlFlow::Break(_) = self.ate(token) {
      // If `ate` returns break, it consumed the expected token and we are done.
      return;
    }
    // Otherwise, start error recovery
    // We can always recover to our expected token, so ensure it's in the anchor set.
    anchor_set.insert(token);
    self.recover_until(anchor_set, vec![token]);
    // We might have recovered to our expected token in which case we want to consume it to get
    // us back on track. We don't want to recurse, because that might not terminate, so we just
    // encode a singularly secondary check.
    let _ = self.ate(token);
  }

  fn atom(&mut self, anchor: HashSet<Syntax>) -> ControlFlow<()> {
    match self.input.peek() {
      Syntax::Identifier => {
        self.with(Syntax::Var, |this| this.expect(Syntax::Identifier, anchor));
      }
      Syntax::Int => {
        self.with(Syntax::IntegerExpr, |this| this.expect(Syntax::Int, anchor));
      }
      Syntax::LeftParen => {
        self.with(Syntax::ParenthesizedExpr, |this| {
          this.expect(Syntax::LeftParen, anchor.clone());
          this.expr(unioning(&anchor, [Syntax::RightParen]));
          this.expect(Syntax::RightParen, anchor);
        });
      }
      Syntax::VerticalBar => {
        self.with(Syntax::Fun, |this| {
          this.expect(Syntax::VerticalBar, anchor.clone());
          this.with(Syntax::FunBinder, |this| {
            this.expect(Syntax::Identifier, anchor.clone())
          });
          this.expect(Syntax::VerticalBar, anchor.clone());
          this.expr(anchor);
        });
      }
      _ => {
        return ControlFlow::Break(());
      }
    };

    ControlFlow::Continue(())
  }

  // A series of applications.
  fn app(&mut self, anchor: HashSet<Syntax>) {
    let checkpoint = self.builder.checkpoint();

    let ControlFlow::Continue(()) = self.atom(anchor.clone()) else {
      // An application must have atleast one atom within it
      self.recover_until(anchor, vec![Syntax::Expr]);
      return;
    };

    let ControlFlow::Continue(()) = self.atom(anchor.clone()) else {
      return;
    };

    self.builder.start_node_at(checkpoint, Syntax::App.into());
    self.builder.finish_node();

    while let ControlFlow::Continue(()) = self.atom(anchor.clone()) {
      self.builder.start_node_at(checkpoint, Syntax::App.into());
      self.builder.finish_node();
    }
  }

  fn let_(&mut self, anchor: HashSet<Syntax>) {
    self.with(Syntax::Let, |this| {
      this.expect(
        Syntax::LetKw,
        unioning(
          &anchor,
          [Syntax::Identifier, Syntax::Equal, Syntax::Semicolon],
        ),
      );
      this.with(Syntax::LetBinder, |this| {
        this.expect(
          Syntax::Identifier,
          unioning(&anchor, [Syntax::Equal, Syntax::Semicolon]),
        )
      });
      this.expect(Syntax::Equal, unioning(&anchor, [Syntax::Semicolon]));
      this.expr(unioning(&anchor, [Syntax::Semicolon]));
      this.expect(Syntax::Semicolon, anchor.clone());
    })
  }

  fn expr(&mut self, anchor: HashSet<Syntax>) {
    self.with(Syntax::Expr, |this| {
      while this.input.at(Syntax::LetKw) {
        this.let_(unioning(&anchor, [Syntax::LetKw]));
      }
      this.app(anchor);
    });
  }

  fn whitespace(&mut self) {
    if !self.input.at(Syntax::Whitespaces) {
      return;
    }
    let Some(span) = self.input.advance() else {
      return;
    };
    self
      .builder
      .token(Syntax::Whitespaces.into(), &self.input.content[span]);
  }

  fn program(&mut self) {
    self.with(Syntax::Program, |this| {
      this.whitespace();
      this.expr(hashset![Syntax::EndOfFile]);
      if !this.input.at(Syntax::EndOfFile) {
        this.recover_until(hashset![], vec![Syntax::EndOfFile]);
      }
    });
  }
}

pub fn parse(input: &str) -> (GreenNode, Vec<ParseError>) {
  let mut parser = Parser::new(input);
  parser.program();
  (parser.builder.finish(), parser.errors)
}

#[cfg(test)]
mod tests {
  use rowan::SyntaxNode;

  use super::*;

  #[test]
  fn parsing_multiple_lets_and_multiple_apps() {
    let input = r#"
let x = |a| a;
let y = |
  b| x b;
y (
  |c| c
   ) 
4
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..56
          Whitespaces@0..1 "\n"
          Expr@1..56
            Let@1..16
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..7
                Identifier@5..6 "x"
                Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..14
                Fun@9..14
                  VerticalBar@9..10 "|"
                  FunBinder@10..11
                    Identifier@10..11 "a"
                  VerticalBar@11..12 "|"
                  Whitespaces@12..13 " "
                  Expr@13..14
                    Var@13..14
                      Identifier@13..14 "a"
              Semicolon@14..15 ";"
              Whitespaces@15..16 "\n"
            Let@16..36
              LetKw@16..19 "let"
              Whitespaces@19..20 " "
              LetBinder@20..22
                Identifier@20..21 "y"
                Whitespaces@21..22 " "
              Equal@22..23 "="
              Whitespaces@23..24 " "
              Expr@24..34
                Fun@24..34
                  VerticalBar@24..25 "|"
                  Whitespaces@25..28 "\n  "
                  FunBinder@28..29
                    Identifier@28..29 "b"
                  VerticalBar@29..30 "|"
                  Whitespaces@30..31 " "
                  Expr@31..34
                    App@31..34
                      Var@31..33
                        Identifier@31..32 "x"
                        Whitespaces@32..33 " "
                      Var@33..34
                        Identifier@33..34 "b"
              Semicolon@34..35 ";"
              Whitespaces@35..36 "\n"
            App@36..56
              App@36..54
                Var@36..38
                  Identifier@36..37 "y"
                  Whitespaces@37..38 " "
                ParenthesizedExpr@38..54
                  LeftParen@38..39 "("
                  Whitespaces@39..42 "\n  "
                  Expr@42..51
                    Fun@42..51
                      VerticalBar@42..43 "|"
                      FunBinder@43..44
                        Identifier@43..44 "c"
                      VerticalBar@44..45 "|"
                      Whitespaces@45..46 " "
                      Expr@46..51
                        Var@46..51
                          Identifier@46..47 "c"
                          Whitespaces@47..51 "\n   "
                  RightParen@51..52 ")"
                  Whitespaces@52..54 " \n"
              IntegerExpr@54..56
                Int@54..55 "4"
                Whitespaces@55..56 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_multiple_applications() {
    let input = r#"f (g 3) 3 4 "#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..12
          Expr@0..12
            App@0..12
              App@0..10
                App@0..8
                  Var@0..2
                    Identifier@0..1 "f"
                    Whitespaces@1..2 " "
                  ParenthesizedExpr@2..8
                    LeftParen@2..3 "("
                    Expr@3..6
                      App@3..6
                        Var@3..5
                          Identifier@3..4 "g"
                          Whitespaces@4..5 " "
                        IntegerExpr@5..6
                          Int@5..6 "3"
                    RightParen@6..7 ")"
                    Whitespaces@7..8 " "
                IntegerExpr@8..10
                  Int@8..9 "3"
                  Whitespaces@9..10 " "
              IntegerExpr@10..12
                Int@10..11 "4"
                Whitespaces@11..12 " "
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_invalid_let() {
    let input = r#"
let x = |a| a |
let y = 3
x y
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..31
          Whitespaces@0..1 "\n"
          Expr@1..31
            Let@1..31
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..7
                Identifier@5..6 "x"
                Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..31
                Fun@9..31
                  VerticalBar@9..10 "|"
                  FunBinder@10..11
                    Identifier@10..11 "a"
                  VerticalBar@11..12 "|"
                  Whitespaces@12..13 " "
                  Expr@13..31
                    App@13..31
                      Var@13..15
                        Identifier@13..14 "a"
                        Whitespaces@14..15 " "
                      Fun@15..31
                        VerticalBar@15..16 "|"
                        Whitespaces@16..17 "\n"
                        FunBinder@17..17
                        Expr@17..31
                          Let@17..31
                            LetKw@17..20 "let"
                            Whitespaces@20..21 " "
                            LetBinder@21..23
                              Identifier@21..22 "y"
                              Whitespaces@22..23 " "
                            Equal@23..24 "="
                            Whitespaces@24..25 " "
                            Expr@25..31
                              App@25..31
                                App@25..29
                                  IntegerExpr@25..27
                                    Int@25..26 "3"
                                    Whitespaces@26..27 "\n"
                                  Var@27..29
                                    Identifier@27..28 "x"
                                    Whitespaces@28..29 " "
                                Var@29..31
                                  Identifier@29..30 "y"
                                  Whitespaces@30..31 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_invalid() {
    let input = r#"
let x_y_2 = ( | x |
    | y | x) 2 (|z test_id | z)
  ;
( | x | x) x_y_2
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..74
          Whitespaces@0..1 "\n"
          Expr@1..74
            Let@1..57
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..11
                Identifier@5..10 "x_y_2"
                Whitespaces@10..11 " "
              Equal@11..12 "="
              Whitespaces@12..13 " "
              Expr@13..55
                App@13..55
                  App@13..36
                    ParenthesizedExpr@13..34
                      LeftParen@13..14 "("
                      Whitespaces@14..15 " "
                      Expr@15..32
                        Fun@15..32
                          VerticalBar@15..16 "|"
                          Whitespaces@16..17 " "
                          FunBinder@17..19
                            Identifier@17..18 "x"
                            Whitespaces@18..19 " "
                          VerticalBar@19..20 "|"
                          Whitespaces@20..25 "\n    "
                          Expr@25..32
                            Fun@25..32
                              VerticalBar@25..26 "|"
                              Whitespaces@26..27 " "
                              FunBinder@27..29
                                Identifier@27..28 "y"
                                Whitespaces@28..29 " "
                              VerticalBar@29..30 "|"
                              Whitespaces@30..31 " "
                              Expr@31..32
                                Var@31..32
                                  Identifier@31..32 "x"
                      RightParen@32..33 ")"
                      Whitespaces@33..34 " "
                    IntegerExpr@34..36
                      Int@34..35 "2"
                      Whitespaces@35..36 " "
                  ParenthesizedExpr@36..55
                    LeftParen@36..37 "("
                    Expr@37..51
                      Fun@37..51
                        VerticalBar@37..38 "|"
                        FunBinder@38..40
                          Identifier@38..39 "z"
                          Whitespaces@39..40 " "
                        Error@40..48
                          Identifier@40..47 "test_id"
                          Whitespaces@47..48 " "
                        VerticalBar@48..49 "|"
                        Whitespaces@49..50 " "
                        Expr@50..51
                          Var@50..51
                            Identifier@50..51 "z"
                    RightParen@51..52 ")"
                    Whitespaces@52..55 "\n  "
              Semicolon@55..56 ";"
              Whitespaces@56..57 "\n"
            App@57..74
              ParenthesizedExpr@57..68
                LeftParen@57..58 "("
                Whitespaces@58..59 " "
                Expr@59..66
                  Fun@59..66
                    VerticalBar@59..60 "|"
                    Whitespaces@60..61 " "
                    FunBinder@61..63
                      Identifier@61..62 "x"
                      Whitespaces@62..63 " "
                    VerticalBar@63..64 "|"
                    Whitespaces@64..65 " "
                    Expr@65..66
                      Var@65..66
                        Identifier@65..66 "x"
                RightParen@66..67 ")"
                Whitespaces@67..68 " "
              Var@68..74
                Identifier@68..73 "x_y_2"
                Whitespaces@73..74 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_let_in_invalid_position() {
    let input = r#"
let y = |x| x;
y let a = 1;
y a 
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..34
          Whitespaces@0..1 "\n"
          Expr@1..18
            Let@1..16
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..7
                Identifier@5..6 "y"
                Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..14
                Fun@9..14
                  VerticalBar@9..10 "|"
                  FunBinder@10..11
                    Identifier@10..11 "x"
                  VerticalBar@11..12 "|"
                  Whitespaces@12..13 " "
                  Expr@13..14
                    Var@13..14
                      Identifier@13..14 "x"
              Semicolon@14..15 ";"
              Whitespaces@15..16 "\n"
            Var@16..18
              Identifier@16..17 "y"
              Whitespaces@17..18 " "
          Error@18..34
            LetKw@18..21 "let"
            Whitespaces@21..22 " "
            Identifier@22..23 "a"
            Whitespaces@23..24 " "
            Equal@24..25 "="
            Whitespaces@25..26 " "
            Int@26..27 "1"
            Semicolon@27..28 ";"
            Whitespaces@28..29 "\n"
            Identifier@29..30 "y"
            Whitespaces@30..31 " "
            Identifier@31..32 "a"
            Whitespaces@32..34 " \n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_recovers_from_missing_semi() {
    let input = r#"
let a = (|x| x)
let b = 3;
a b
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..32
          Whitespaces@0..1 "\n"
          Expr@1..32
            Let@1..17
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..7
                Identifier@5..6 "a"
                Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..17
                ParenthesizedExpr@9..17
                  LeftParen@9..10 "("
                  Expr@10..15
                    Fun@10..15
                      VerticalBar@10..11 "|"
                      FunBinder@11..12
                        Identifier@11..12 "x"
                      VerticalBar@12..13 "|"
                      Whitespaces@13..14 " "
                      Expr@14..15
                        Var@14..15
                          Identifier@14..15 "x"
                  RightParen@15..16 ")"
                  Whitespaces@16..17 "\n"
            Let@17..28
              LetKw@17..20 "let"
              Whitespaces@20..21 " "
              LetBinder@21..23
                Identifier@21..22 "b"
                Whitespaces@22..23 " "
              Equal@23..24 "="
              Whitespaces@24..25 " "
              Expr@25..26
                IntegerExpr@25..26
                  Int@25..26 "3"
              Semicolon@26..27 ";"
              Whitespaces@27..28 "\n"
            App@28..32
              Var@28..30
                Identifier@28..29 "a"
                Whitespaces@29..30 " "
              Var@30..32
                Identifier@30..31 "b"
                Whitespaces@31..32 "\n"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));
  }

  #[test]
  fn parse_test_missing_expr_after_let() {
    let input = r#"
let a = (|x| x);
"#;
    let (tree, _) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..18
          Whitespaces@0..1 "\n"
          Expr@1..18
            Let@1..18
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..7
                Identifier@5..6 "a"
                Whitespaces@6..7 " "
              Equal@7..8 "="
              Whitespaces@8..9 " "
              Expr@9..16
                ParenthesizedExpr@9..16
                  LeftParen@9..10 "("
                  Expr@10..15
                    Fun@10..15
                      VerticalBar@10..11 "|"
                      FunBinder@11..12
                        Identifier@11..12 "x"
                      VerticalBar@12..13 "|"
                      Whitespaces@13..14 " "
                      Expr@14..15
                        Var@14..15
                          Identifier@14..15 "x"
                  RightParen@15..16 ")"
              Semicolon@16..17 ";"
              Whitespaces@17..18 "\n"
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
              ParenthesizedExpr@0..3
                LeftParen@0..1 "("
                Expr@1..1
                RightParen@1..2 ")"
                Whitespaces@2..3 " "
              Var@3..4
                Identifier@3..4 "b"
    "#]];
    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));

    let expect_errors = expect_test::expect!["[ParseError { expected: [Expr], span: 1..2 }]"];
    expect_errors.assert_eq(&format!("{errors:?}"));
  }

  #[test]
  fn parse_test_recover_within_let_defn() {
    let input = r#"
let apply = |fun||arg| fun arg;
let z = apply = ;
apply (|x| x)
"#;
    let (tree, errors) = parse(input);
    let expect = expect_test::expect![[r#"
        Program@0..65
          Whitespaces@0..1 "\n"
          Expr@1..65
            Let@1..33
              LetKw@1..4 "let"
              Whitespaces@4..5 " "
              LetBinder@5..11
                Identifier@5..10 "apply"
                Whitespaces@10..11 " "
              Equal@11..12 "="
              Whitespaces@12..13 " "
              Expr@13..31
                Fun@13..31
                  VerticalBar@13..14 "|"
                  FunBinder@14..17
                    Identifier@14..17 "fun"
                  VerticalBar@17..18 "|"
                  Expr@18..31
                    Fun@18..31
                      VerticalBar@18..19 "|"
                      FunBinder@19..22
                        Identifier@19..22 "arg"
                      VerticalBar@22..23 "|"
                      Whitespaces@23..24 " "
                      Expr@24..31
                        App@24..31
                          Var@24..28
                            Identifier@24..27 "fun"
                            Whitespaces@27..28 " "
                          Var@28..31
                            Identifier@28..31 "arg"
              Semicolon@31..32 ";"
              Whitespaces@32..33 "\n"
            Let@33..51
              LetKw@33..36 "let"
              Whitespaces@36..37 " "
              LetBinder@37..39
                Identifier@37..38 "z"
                Whitespaces@38..39 " "
              Equal@39..40 "="
              Whitespaces@40..41 " "
              Expr@41..47
                Var@41..47
                  Identifier@41..46 "apply"
                  Whitespaces@46..47 " "
              Error@47..49
                Equal@47..48 "="
                Whitespaces@48..49 " "
              Semicolon@49..50 ";"
              Whitespaces@50..51 "\n"
            App@51..65
              Var@51..57
                Identifier@51..56 "apply"
                Whitespaces@56..57 " "
              ParenthesizedExpr@57..65
                LeftParen@57..58 "("
                Expr@58..63
                  Fun@58..63
                    VerticalBar@58..59 "|"
                    FunBinder@59..60
                      Identifier@59..60 "x"
                    VerticalBar@60..61 "|"
                    Whitespaces@61..62 " "
                    Expr@62..63
                      Var@62..63
                        Identifier@62..63 "x"
                RightParen@63..64 ")"
                Whitespaces@64..65 "\n"
    "#]];

    expect.assert_eq(&format!("{:#?}", SyntaxNode::<Lang>::new_root(tree)));

    let expect_errors =
      expect_test::expect!["[ParseError { expected: [Semicolon], span: 47..49 }]"];
    expect_errors.assert_eq(&format!("{errors:?}"));
  }
}
