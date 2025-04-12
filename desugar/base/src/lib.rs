use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Range;

use parser_base::rowan::{GreenNode, NodeOrToken, TextRange};
use parser_base::{
  Lang, Syntax, SyntaxNode,
};
use types_base::{Ast, NodeId};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ErrorKind {
  MissingSyntax(Syntax),
  ProgramMissingExpr,
  ExpectedLetOrAppInExpr(Syntax),
  LetMissingBinding,
  LetMissingExpr,
  Unexpected(Vec<Syntax>),
  InvalidInt(std::num::ParseIntError),
  FunMissingIdentifier,
  FunMissingExpr,
  EmptyApplication,
  VarMissingIdentifier,
  IntegerExprMissingInt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DesugarError {
  pub kind: ErrorKind,
  pub span: Range<usize>,
}

impl DesugarError {
  fn new(kind: ErrorKind, span: Range<usize>) -> Self {
    Self { kind, span }
  }
}

struct Desugar {
  node_id: u32,
  ast_to_cst: HashMap<NodeId, SyncNode>,
  root: GreenNode,
}

impl Desugar {
  fn new(root: GreenNode) -> Self {
    Self {
      node_id: 0,
      ast_to_cst: HashMap::default(),
      root,
    }
  }

  fn next_id(&mut self) -> NodeId {
    let id = self.node_id;
    self.node_id += 1;
    NodeId(id)
  }

  fn insert_node(&mut self, node_id: NodeId, span: TextRange) -> Option<SyncNode> {
    self.ast_to_cst.insert(node_id, SyncNode { root: self.root.clone(), span })
  }

  fn desugar_program(&mut self, cst: SyntaxNode<Lang>) -> Result<Ast<String>, DesugarError> {
    let Some(expr) = cst.first_child() else {
      return Err(DesugarError::new(
        ErrorKind::ProgramMissingExpr,
        cst.text_range().into(),
      ));
    };

    self.desugar_expr(expr)
  }

  fn desugar_expr(
    &mut self,
    expr: SyntaxNode<Lang>,
  ) -> Result<Ast<String>, DesugarError> {
    if expr.kind() != Syntax::Expr {
      return Err(DesugarError::new(
        ErrorKind::MissingSyntax(Syntax::Expr),
        expr.text_range().into(),
      ));
    }

    let mut binds = vec![];
    // The only tokens that appear in Lets are whitespace that we are happy to skip here.
    for child in expr.children() {
      match child.kind() {
        Syntax::Let => {
          let (var, arg) = self.desugar_let(child.clone())?;
          binds.push((var, arg, child))
        },
        Syntax::App => {
          let app = self.desugar_app_spine(child)?;
          return Ok(binds.into_iter().rfold(app, |body, (var, arg, child)| {
            let app_id = self.next_id();
            let fun_id = self.next_id();
            self.insert_node(app_id, child.text_range());
            self.insert_node(fun_id, child.text_range());
            Ast::app(app_id, Ast::fun(fun_id, var, body), arg)
          }));
        },
        _ => {
          return Err(DesugarError::new(
            ErrorKind::ExpectedLetOrAppInExpr(child.kind()),
            child.text_range().into(),
          ));
        }
      }
    }

    Err(DesugarError::new(
      ErrorKind::MissingSyntax(Syntax::App),
      expr
        .last_child_or_token()
        .unwrap_or(NodeOrToken::Node(expr))
        .text_range()
        .into(),
    ))
  }

  fn desugar_let(
    &mut self,
    bind: SyntaxNode<Lang>,
  ) -> Result<(String, Ast<String>), DesugarError> {
    let mut children = bind.children();

    let Some(var) = children.next() else {
      return Err(DesugarError::new(
        ErrorKind::LetMissingBinding,
        bind.text_range().into(),
      ));
    };

    let Some(binder) = (var.kind() == Syntax::LetBinder)
      .then_some(())
      .and_then(|_| var.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier))
    else {
      return Err(DesugarError::new(
        ErrorKind::LetMissingBinding,
        var.text_range().into(),
      ));
    };

    let id = binder.to_string();

    let Some(expr) = children.next() else {
      return Err(DesugarError::new(
        ErrorKind::LetMissingExpr,
        bind.text_range().into()
      ));
    };

    let ast = self.desugar_expr(expr)?;

    let extra = children.map(|node| node.kind()).collect::<Vec<_>>();
    if !extra.is_empty() {
      return Err(DesugarError::new(
        ErrorKind::Unexpected(extra),
        bind.text_range().into(),
      ));
    }

    Ok((id, ast))
  }
  
  fn desugar_fun(&mut self, fun: SyntaxNode<Lang>) -> Result<Ast<String>, DesugarError> {
    let Some(var) = fun.first_child_by_kind(&|kind| kind == Syntax::FunBinder) else {
      return Err(DesugarError::new(
        ErrorKind::FunMissingIdentifier,
        fun.first_child_or_token().map(|n| n.text_range()).unwrap_or(fun.text_range()).into()
      ));
    };

    let Some(expr) = fun.first_child_by_kind(&|kind| kind == Syntax::Expr) else {
      return Err(DesugarError::new(
        ErrorKind::FunMissingIdentifier,
        fun.last_child_or_token().map(|n| n.text_range()).unwrap_or(fun.text_range()).into()
      ));
    };

    let body = self.desugar_expr(expr)?;

    let id = self.next_id();
    Ok(Ast::fun(id, var.to_string(), body))
  }

  fn desugar_app_spine(&mut self, app: SyntaxNode<Lang>) -> Result<Ast<String>, DesugarError> {
    let mut spine = vec![];

    for atom in app.children() {
      let expr = match atom.kind() {
        Syntax::Fun => self.desugar_fun(atom)?,
        Syntax::ParenthesizedExpr => {
          atom.first_child_by_kind(&|kind| kind == Syntax::Expr)
              .ok_or(DesugarError::new(
                ErrorKind::MissingSyntax(Syntax::Expr),
                atom.text_range().into()
              ))
              .and_then(|expr| self.desugar_expr(expr))?
        },
        Syntax::Var => {
          let var = atom
            .first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier)
            .ok_or(DesugarError::new(
              ErrorKind::VarMissingIdentifier,
              atom.text_range().into()
            ))?;
          let id = self.next_id();
          self.insert_node(id, atom.text_range());
          Ast::Var(id, var.to_string())
        },
        Syntax::IntegerExpr => {
          let int = atom
              .first_child_or_token_by_kind(&|kind| kind == Syntax::Int)
              .ok_or(DesugarError::new(
                ErrorKind::IntegerExprMissingInt,
                atom.text_range().into()
              ))?;
          let id = self.next_id();
          let val = int.to_string().parse().map_err(|err| DesugarError::new(
            ErrorKind::InvalidInt(err),
            int.text_range().into()
          ))?;
          self.insert_node(id, atom.text_range());
          Ast::Int(id, val)
        },
        _ => return Err(DesugarError::new(ErrorKind::Unexpected(vec![atom.kind()]), atom.text_range().into())),
      };
      spine.push(expr);
    }
    
    spine
      .into_iter()
      .reduce(|a, b| {
        let id = self.next_id();
        self.insert_node(id, app.text_range());
        Ast::app(id, a, b)
      })
      .ok_or(DesugarError::new(ErrorKind::EmptyApplication, app.text_range().into()))
  }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct SyncNode {
  pub root: GreenNode,
  pub span: TextRange
}

// TODO: Combine content and tree into one output of parsing.
// Possibly with an API
pub fn desugar(
  root: GreenNode,
) -> Result<(Ast<String>, HashMap<NodeId, SyncNode>), DesugarError> {
  let mut desugar = Desugar::new(root.clone());
  let ast = desugar.desugar_program(SyntaxNode::new_root(root))?;
  Ok((ast, desugar.ast_to_cst))
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_base::builder::AstBuilder;

  fn desugar(input: &str) -> Result<Ast<String>, DesugarError> {
    let (cst, _) = parser_base::parse(input);
    crate::desugar(cst).map(|(ast, _)| ast)
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

    // It just so happens our AstBuilder assigns IDs the same way as our desugar pass, so this
    // works.
    let b = AstBuilder::default();
    assert_eq!(
      ast,
      b.locals(
        [
          (
            "x".to_string(),
            b.fun("a".to_string(), b.var("a".to_string()))
          ),
          (
            "y".to_string(),
            b.fun(
              "b".to_string(),
              b.app(b.var("x".to_string()), b.var("b".to_string()))
            )
          )
        ],
        b.apps(
          b.var("y".to_string()),
          [b.fun("c".to_string(), b.var("c".to_string())), b.int(4)]
        )
      ),
    );
  }
}
