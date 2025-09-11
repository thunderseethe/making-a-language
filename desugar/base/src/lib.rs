use std::collections::HashMap;
use std::fmt::Debug;

use parser_base::{rowan::{ast::SyntaxNodePtr, GreenNode, SyntaxNode}, Lang, Syntax};
use types_base::{Ast, NodeId};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DesugarError {
  MissingSyntax(Syntax),
  LetMissingBinding,
  LetMissingExpr,
  InvalidInt(std::num::ParseIntError),
  FunMissingExpr,
  ApplicationMissingFun,
  ApplicationMissingArg,
  VarMissingIdentifier,
  IntegerExprMissingInt,
  ExprMissingBody,
  UnexpectedInExpr(String),
  UnexpectedAtom(Syntax),
}

struct Desugar {
  node_id: u32,
  ast_to_cst: HashMap<NodeId, SyncNode>,
  errors: HashMap<SyntaxNodePtr<Lang>, DesugarError>,
  root: GreenNode,
}

impl Desugar {
  fn new(root: GreenNode) -> Self {
    Self {
      node_id: 0,
      ast_to_cst: HashMap::default(),
      errors: HashMap::default(),
      root,
    }
  }

  fn next_id(&mut self) -> NodeId {
    let id = self.node_id;
    self.node_id += 1;
    NodeId(id)
  }

  fn insert_node(&mut self, node_id: NodeId, ptr: SyntaxNodePtr<Lang>) -> Option<SyncNode> {
    self.ast_to_cst.insert(
      node_id,
      SyncNode {
        root: self.root.clone(),
        ptr,
      },
    )
  }

  fn hole(&mut self, node: &SyntaxNode<Lang>) -> Ast<String> {
    let id = self.next_id();
    self.insert_node(id, SyntaxNodePtr::new(node));
    Ast::Hole(id, "_".to_string())
  }

  fn emit_error(&mut self, node: &SyntaxNode<Lang>, kind: DesugarError) -> Option<DesugarError> {
    self.errors.insert(SyntaxNodePtr::new(node), kind)
  }

  fn error_hole(&mut self, node: &SyntaxNode<Lang>, kind: DesugarError) -> Ast<String> {
    self.emit_error(node, kind);
    self.hole(node)
  }

  fn desugar_program(&mut self, cst: SyntaxNode<Lang>) -> Ast<String> {
    let Some(expr) = cst.first_child() else {
      // Assume parser has emitted an error for the missing node and just return a Hole here.
      return self.hole(&cst);
    };

    self.desugar_expr(expr)
  }

  fn build_locals(
    &mut self,
    binds: Vec<(String, Ast<String>, SyntaxNode<Lang>)>,
    body: Ast<String>,
  ) -> Ast<String> {
    binds.into_iter().rfold(body, |body, (var, arg, child)| {
      let app_id = self.next_id();
      let fun_id = self.next_id();
      if let Some(let_binder) = child.first_child_by_kind(&|kind| kind == Syntax::LetBinder) {
        self.insert_node(fun_id, SyntaxNodePtr::new(&let_binder));
      }
      self.insert_node(app_id, SyntaxNodePtr::new(&child));
      Ast::app(app_id, Ast::fun(fun_id, var, body), arg)
    })
  }

  fn desugar_expr(&mut self, expr: SyntaxNode<Lang>) -> Ast<String> {
    if expr.kind() != Syntax::Expr {
      return self.error_hole(&expr, DesugarError::MissingSyntax(Syntax::Expr));
    }

    let mut binds = vec![];
    // The only tokens that appear in Lets are whitespace that we are happy to skip here.
    for child in expr.children() {
      match child.kind() {
        Syntax::Let => match self.desugar_let(child.clone()) {
          Ok((var, arg)) => binds.push((var, arg, child)),
          Err(error) => {
            let hole = self.error_hole(&child, error);
            return self.build_locals(binds, hole);
          }
        },
        _ => {
          let body = self.desugar_app(child);
          return self.build_locals(binds, body);
        }
      }
    }

    let node = &expr.last_child().unwrap_or(expr);
    self.error_hole(node, DesugarError::ExprMissingBody)
  }

  fn desugar_let(&mut self, bind: SyntaxNode<Lang>) -> Result<(String, Ast<String>), DesugarError> {
    let mut children = bind.children();

    let Some(var) = children.next() else {
      return Err(DesugarError::LetMissingBinding);
    };

    let Some(binder) = (var.kind() == Syntax::LetBinder)
      .then_some(())
      .and_then(|_| var.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier))
    else {
      return Err(DesugarError::LetMissingBinding);
    };

    let id = binder.to_string();

    let ast = match children.next() {
      Some(expr) => self.desugar_expr(expr),
      None => self.error_hole(&bind, DesugarError::LetMissingExpr),
    };

    Ok((id, ast))
  }

  fn desugar_fun(&mut self, fun: SyntaxNode<Lang>) -> Ast<String> {
    let Some(var) = fun
      .first_child_by_kind(&|kind| kind == Syntax::FunBinder)
      .and_then(|node| node.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier))
    else {
      self.emit_error(&fun, DesugarError::MissingSyntax(Syntax::FunBinder));
      return self.hole(&fun);
    };

    let body = match fun.first_child_by_kind(&|kind| kind == Syntax::Expr) {
      Some(expr) => self.desugar_expr(expr),
      None => self.error_hole(&fun, DesugarError::FunMissingExpr),
    };

    let id = self.next_id();
    self.insert_node(id, SyntaxNodePtr::new(&fun));
    println!("var: \"{var}\"");
    Ast::fun(id, var.to_string(), body)
  }

  fn desugar_app(&mut self, app: SyntaxNode<Lang>) -> Ast<String> {
    // Handle the case where our application is a single expression, rather than a function and
    // argument.
    let Syntax::App = app.kind() else {
      return self.desugar_atom(app);
    };

    let fun = match app.first_child() {
      Some(fun) => self.desugar_app(fun),
      None => self.error_hole(&app, DesugarError::ApplicationMissingFun),
    };

    let arg = match app.last_child() {
      Some(arg) => self.desugar_atom(arg),
      None => self.error_hole(&app, DesugarError::ApplicationMissingArg),
    };

    let id = self.next_id();
    self.insert_node(id, SyntaxNodePtr::new(&app));
    Ast::app(id, fun, arg)
  }

  fn desugar_atom(&mut self, atom: SyntaxNode<Lang>) -> Ast<String> {
    match atom.kind() {
      Syntax::Fun => self.desugar_fun(atom),
      Syntax::ParenthesizedExpr => match atom.first_child_by_kind(&|kind| kind == Syntax::Expr) {
        Some(expr) => self.desugar_expr(expr),
        None => self.error_hole(&atom, DesugarError::MissingSyntax(Syntax::Expr)),
      },
      Syntax::Var => {
        let Some(var) = atom.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier)
        else {
          return self.error_hole(&atom, DesugarError::VarMissingIdentifier);
        };
        let id = self.next_id();
        self.insert_node(id, SyntaxNodePtr::new(&atom));
        Ast::Var(id, var.to_string())
      }
      Syntax::IntegerExpr => {
        let Some(int) = atom.first_child_or_token_by_kind(&|kind| kind == Syntax::Int) else {
          return self.error_hole(&atom, DesugarError::IntegerExprMissingInt);
        };

        let id = self.next_id();
        let val = match int.to_string().parse() {
          Ok(int) => int,
          Err(err) => return self.error_hole(&atom, DesugarError::InvalidInt(err)),
        };
        self.insert_node(id, SyntaxNodePtr::new(&atom));
        Ast::Int(id, val)
      }
      _ => self.error_hole(&atom, DesugarError::UnexpectedAtom(atom.kind())),
    }
  }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct SyncNode {
  pub root: GreenNode,
  pub ptr: SyntaxNodePtr<Lang>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DesugarOut {
  pub ast: Ast<String>,
  pub ast_to_cst: HashMap<NodeId, SyncNode>,
  pub errors: HashMap<SyntaxNodePtr<Lang>, DesugarError>,
}

// TODO: Combine content and tree into one output of parsing.
// Possibly with an API
pub fn desugar(root: GreenNode) -> DesugarOut {
  let mut desugar = Desugar::new(root.clone());
  let ast = desugar.desugar_program(SyntaxNode::new_root(root));
  DesugarOut {
    ast,
    ast_to_cst: desugar.ast_to_cst,
    errors: desugar.errors,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_base::builder::AstBuilder;

  fn desugar(input: &str) -> (Ast<String>, HashMap<SyntaxNodePtr<Lang>, DesugarError>) {
    let (cst, _) = parser_base::parse(input);
    let out = crate::desugar(cst);
    (out.ast, out.errors)
  }

  #[test]
  fn desugar_ast() {
    let input = r#"
let x = \a -> a;
let y = \ 
  b -> x b;
y (
  \c -> c
   )
4
"#;

    let (ast, _) = desugar(input);

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
