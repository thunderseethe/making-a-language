use std::iter::Peekable;
use std::ops::ControlFlow;

use logos::{Logos, SpannedIter};
use syntree::{Builder, FlavorDefault, Tree};

#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
  #[token("(")]
  LeftParen,
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
}

struct Input<'a> {
  content: &'a str,
  lexer: Peekable<SpannedIter<'a, Token>>,
}

impl<'a> Input<'a> {
  fn new(content: &'a str) -> Self {
    Self {
      content,
      lexer: Token::lexer(content).spanned().peekable(),
    }
  }

  fn peek(&mut self) -> Token {
    self.lexer.peek().map(|(tok, span)| match tok {
      Ok(tok) => tok,
      Err(_) => panic!("{}", &self.content[span.start..span.end]),
    }).copied().unwrap_or(Token::EndOfFile)
    /*let mut iter = &mut self.lexer;
    self.lookahead.get_or_insert_with(|| iter.next())
      .as_ref()
      .copied()
      .map(|(tok, _)| match tok {
        
      })
      .unwrap_or(Token::EndOfFile)*/
  }

  fn at(&mut self, token: Token) -> bool {
    self.peek() == token
  }

  fn advance(&mut self) -> Option<usize> { 
    let (_, span) = self.lexer.next()?;
    Some(span.end - span.start)
  }

  fn eat(&mut self, token: Token) -> Option<usize> {
    if self.at(token) {
      self.advance()
    } else {
      None
    }
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Node {
  Fun,
  App,
  ParenthesizedExpr,
  Var,
  Let,
  Lets,
  Program,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Syntax {
  Error(&'static str),
  Token(Token),
  Node(Node),
}

struct Parser<'a> {
  input: Input<'a>,
  builder: Builder<Syntax, FlavorDefault>,
}

impl<'a> Parser<'a> {
  fn new(content: &'a str) -> Self {
    Self {
      input: Input::new(content),
      builder: Builder::default(),
    }
  }

  fn with<T>(&mut self, node: Node, body: impl FnOnce(&mut Self) -> T) -> T {
    self.builder.open(Syntax::Node(node)).unwrap();

    let res = body(self);
    
    self.builder.close().unwrap();

    res
  }

  fn expect(&mut self, token: Token) -> Option<usize> {
    match self.input.eat(token) {
      Some(len) => {
        self.builder.token(Syntax::Token(token), len).unwrap();
        Some(len)
      },
      None => {
        if let Some(len) = self.input.advance() {
          self.builder.token(Syntax::Error("unexpected token"), len).unwrap();
        }
        None
      },
    }
  }

  fn atom(&mut self) -> ControlFlow<()> {
    match self.input.peek() {
      Token::LeftParen => {
          self.with(Node::ParenthesizedExpr, |this| {
            this.expect(Token::LeftParen);
            this.whitespace();
            this.expr();
            this.whitespace();
            this.expect(Token::RightParen);
          });
      },
      Token::Backslash => {
        self.with(Node::Fun, |this| {
          this.expect(Token::Backslash);
          this.whitespace();
          this.expect(Token::Identifier);
          this.whitespace();
          this.expect(Token::Arrow);
          this.whitespace();
          this.expr();
          this.whitespace();
        });
      },
      Token::Identifier => {
        self.with(Node::Var, |this| {
          this.expect(Token::Identifier)
        });
      },
      Token::Int => {
        self.expect(Token::Int);
      }
      _ => {
        return ControlFlow::Break(());
      }
    };

    ControlFlow::Continue(())
  }

  // A series of applications.
  fn app(&mut self) {
    self.with(Node::App, |this| {
      while let ControlFlow::Continue(()) = this.atom() {
        this.whitespace();
      }
    })
  }

  fn expr(&mut self) {
    self.with(Node::Lets, |this| {
      this.whitespace();
      while this.input.at(Token::LetKw) {
        this.with(Node::Let, |this| {
          this.expect(Token::LetKw);
          this.whitespace();
          this.expect(Token::Identifier);
          this.whitespace();
          this.expect(Token::Equal);
          this.whitespace();
          this.expr();
          this.whitespace();
          this.expect(Token::Semicolon);
          this.whitespace();
        })
      };

      // A series of lets is ended by an application.
      this.app();
    })
  }

  fn whitespace(&mut self) {
    if self.input.at(Token::Whitespaces) {
      if let Some(len) = self.input.advance() {
        self.builder.token(Syntax::Token(Token::Whitespaces), len).unwrap();
      }
    }
  }

  fn parse(mut self) -> Tree<Syntax, FlavorDefault> {
    self.with(Node::Program, |this| {
      this.expr();
    });
    self.builder.build().unwrap()
  }
}

pub fn parse(input: &str) -> Tree<Syntax, FlavorDefault> {
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
    let tree = parse(input);
    let mut out = vec![];
    syntree::print::print_with_source(&mut out, &tree, input).unwrap();
    let expect = expect_test::expect![[r#"
        Node(Program)@0..63
          Node(Lets)@0..63
            Token(Whitespaces)@0..1 "\n"
            Node(Let)@1..18
              Token(LetKw)@1..4 "let"
              Token(Whitespaces)@4..5 " "
              Token(Identifier)@5..6 "x"
              Token(Whitespaces)@6..7 " "
              Token(Equal)@7..8 "="
              Token(Whitespaces)@8..9 " "
              Node(Lets)@9..16
                Node(App)@9..16
                  Node(Fun)@9..16
                    Token(Backslash)@9..10 "\\"
                    Token(Identifier)@10..11 "a"
                    Token(Whitespaces)@11..12 " "
                    Token(Arrow)@12..14 "->"
                    Token(Whitespaces)@14..15 " "
                    Node(Lets)@15..16
                      Node(App)@15..16
                        Node(Var)@15..16
                          Token(Identifier)@15..16 "a"
              Token(Semicolon)@16..17 ";"
              Token(Whitespaces)@17..18 "\n"
            Node(Let)@18..41
              Token(LetKw)@18..21 "let"
              Token(Whitespaces)@21..22 " "
              Token(Identifier)@22..23 "y"
              Token(Whitespaces)@23..24 " "
              Token(Equal)@24..25 "="
              Token(Whitespaces)@25..26 " "
              Node(Lets)@26..39
                Node(App)@26..39
                  Node(Fun)@26..39
                    Token(Backslash)@26..27 "\\"
                    Token(Whitespaces)@27..31 " \n  "
                    Token(Identifier)@31..32 "b"
                    Token(Whitespaces)@32..33 " "
                    Token(Arrow)@33..35 "->"
                    Token(Whitespaces)@35..36 " "
                    Node(Lets)@36..39
                      Node(App)@36..39
                        Node(Var)@36..37
                          Token(Identifier)@36..37 "x"
                        Token(Whitespaces)@37..38 " "
                        Node(Var)@38..39
                          Token(Identifier)@38..39 "b"
              Token(Semicolon)@39..40 ";"
              Token(Whitespaces)@40..41 "\n"
            Node(App)@41..63
              Node(Var)@41..42
                Token(Identifier)@41..42 "y"
              Token(Whitespaces)@42..43 " "
              Node(ParenthesizedExpr)@43..59
                Token(LeftParen)@43..44 "("
                Token(Whitespaces)@44..47 "\n  "
                Node(Lets)@47..58
                  Node(App)@47..58
                    Node(Fun)@47..58
                      Token(Backslash)@47..48 "\\"
                      Token(Identifier)@48..49 "c"
                      Token(Whitespaces)@49..50 " "
                      Token(Arrow)@50..52 "->"
                      Token(Whitespaces)@52..53 " "
                      Node(Lets)@53..58
                        Node(App)@53..58
                          Node(Var)@53..54
                            Token(Identifier)@53..54 "c"
                          Token(Whitespaces)@54..58 "\n   "
                Token(RightParen)@58..59 ")"
              Token(Whitespaces)@59..61 " \n"
              Token(Int)@61..62 "4"
              Token(Whitespaces)@62..63 "\n"
    "#]];
    expect.assert_eq(&String::from_utf8(out).unwrap());
  }

  #[test]
  fn parse_invalid_let() {
    let input = r#"
let x = \a -> a ->
let y = 3
x y
"#;
    let tree = parse(input);
    let mut out = vec![];
    syntree::print::print_with_source(&mut out, &tree, input).unwrap();

    let expect = expect_test::expect![[r#"
        Node(Program)@0..34
          Node(Lets)@0..34
            Token(Whitespaces)@0..1 "\n"
            Node(Let)@1..20
              Token(LetKw)@1..4 "let"
              Token(Whitespaces)@4..5 " "
              Token(Identifier)@5..6 "x"
              Token(Whitespaces)@6..7 " "
              Token(Equal)@7..8 "="
              Token(Whitespaces)@8..9 " "
              Node(Lets)@9..17
                Node(App)@9..17
                  Node(Fun)@9..17
                    Token(Backslash)@9..10 "\\"
                    Token(Identifier)@10..11 "a"
                    Token(Whitespaces)@11..12 " "
                    Token(Arrow)@12..14 "->"
                    Token(Whitespaces)@14..15 " "
                    Node(Lets)@15..17
                      Node(App)@15..17
                        Node(Var)@15..16
                          Token(Identifier)@15..16 "a"
                        Token(Whitespaces)@16..17 " "
              Error("unexpected token")@17..19 "->"
              Token(Whitespaces)@19..20 "\n"
            Node(Let)@20..34
              Token(LetKw)@20..23 "let"
              Token(Whitespaces)@23..24 " "
              Token(Identifier)@24..25 "y"
              Token(Whitespaces)@25..26 " "
              Token(Equal)@26..27 "="
              Token(Whitespaces)@27..28 " "
              Node(Lets)@28..34
                Node(App)@28..34
                  Token(Int)@28..29 "3"
                  Token(Whitespaces)@29..30 "\n"
                  Node(Var)@30..31
                    Token(Identifier)@30..31 "x"
                  Token(Whitespaces)@31..32 " "
                  Node(Var)@32..33
                    Token(Identifier)@32..33 "y"
                  Token(Whitespaces)@33..34 "\n"
            Node(App)@34..34 ""
    "#]];
    expect.assert_eq(&String::from_utf8(out).unwrap());
  }

  #[test]
  fn parse_invalid() {
    let input = r#"
let x_y_2 = ( \ x -> 
    \ y -> x) 2 (\z test_id -> z)
  ;
( \ x -> x) x_y_2
"#;
    let tree = parse(input);
    let mut out = vec![];
    syntree::print::print_with_source(&mut out, &tree, input).unwrap();

    let expect = expect_test::expect![[r#"
        Node(Program)@0..59
          Node(Lets)@0..59
            Token(Whitespaces)@0..1 "\n"
            Node(Let)@1..59
              Token(LetKw)@1..4 "let"
              Token(Whitespaces)@4..5 " "
              Token(Identifier)@5..10 "x_y_2"
              Token(Whitespaces)@10..11 " "
              Token(Equal)@11..12 "="
              Token(Whitespaces)@12..13 " "
              Node(Lets)@13..55
                Node(App)@13..55
                  Node(ParenthesizedExpr)@13..36
                    Token(LeftParen)@13..14 "("
                    Token(Whitespaces)@14..15 " "
                    Node(Lets)@15..35
                      Node(App)@15..35
                        Node(Fun)@15..35
                          Token(Backslash)@15..16 "\\"
                          Token(Whitespaces)@16..17 " "
                          Token(Identifier)@17..18 "x"
                          Token(Whitespaces)@18..19 " "
                          Token(Arrow)@19..21 "->"
                          Token(Whitespaces)@21..27 " \n    "
                          Node(Lets)@27..35
                            Node(App)@27..35
                              Node(Fun)@27..35
                                Token(Backslash)@27..28 "\\"
                                Token(Whitespaces)@28..29 " "
                                Token(Identifier)@29..30 "y"
                                Token(Whitespaces)@30..31 " "
                                Token(Arrow)@31..33 "->"
                                Token(Whitespaces)@33..34 " "
                                Node(Lets)@34..35
                                  Node(App)@34..35
                                    Node(Var)@34..35
                                      Token(Identifier)@34..35 "x"
                    Token(RightParen)@35..36 ")"
                  Token(Whitespaces)@36..37 " "
                  Token(Int)@37..38 "2"
                  Token(Whitespaces)@38..39 " "
                  Node(ParenthesizedExpr)@39..53
                    Token(LeftParen)@39..40 "("
                    Node(Lets)@40..51
                      Node(App)@40..51
                        Node(Fun)@40..51
                          Token(Backslash)@40..41 "\\"
                          Token(Identifier)@41..42 "z"
                          Token(Whitespaces)@42..43 " "
                          Error("unexpected token")@43..50 "test_id"
                          Token(Whitespaces)@50..51 " "
                          Node(Lets)@51..51
                            Node(App)@51..51 ""
                    Error("unexpected token")@51..53 "->"
                  Token(Whitespaces)@53..54 " "
                  Node(Var)@54..55
                    Token(Identifier)@54..55 "z"
              Error("unexpected token")@55..56 ")"
              Token(Whitespaces)@56..59 "\n  "
            Node(App)@59..59 ""
    "#]];
    expect.assert_eq(&String::from_utf8(out).unwrap());
  }
}
