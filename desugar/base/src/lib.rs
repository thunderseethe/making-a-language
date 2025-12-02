use std::collections::HashMap;
use std::fmt::Debug;

use parser_base::{
  Lang, Syntax,
  rowan::{GreenNode, SyntaxNode, ast::SyntaxNodePtr},
};
use types_base::{Ast, NodeId};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DesugarError {
  MissingSyntax(Syntax),
  LetMissingBinding,
  LetMissingExpr,
  InvalidInt(std::num::ParseIntError),
  FunMissingBinding,
  FunMissingExpr,
  ApplicationMissingFun,
  ApplicationMissingArg,
  VarMissingIdentifier,
  IntegerExprMissingInt,
  ExprMissingBody,
  UnexpectedAtom(Syntax),
}

struct Desugar {
  node_id: u32,
  root: GreenNode,
  ast_to_cst: HashMap<NodeId, SyntaxNodeHandle>,
  errors: HashMap<SyntaxNodePtr<Lang>, DesugarError>,
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

  fn insert_node(&mut self, node_id: NodeId, ptr: SyntaxNodePtr<Lang>) -> Option<SyntaxNodeHandle> {
    self.ast_to_cst.insert(
      node_id,
      SyntaxNodeHandle {
        root: self.root.clone(),
        ptr,
      },
    )
  }

  fn hole(&mut self, node: &SyntaxNode<Lang>, kind: DesugarError) -> Ast<String> {
    let ptr = SyntaxNodePtr::new(node);
    self.errors.insert(ptr, kind);

    let id = self.next_id();
    self.insert_node(id, ptr);
    Ast::Hole(id, "_".to_string())
  }

  fn desugar_program(&mut self, cst: SyntaxNode<Lang>) -> Ast<String> {
    let Some(expr) = cst.first_child_by_kind(&|kind| kind == Syntax::Expr) else {
      // Assume parser has emitted an error for the missing node and just return a Hole here.
      return self.hole(&cst, DesugarError::MissingSyntax(Syntax::Expr));
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
    let mut binds = vec![];
    // The only tokens that appear in Lets are whitespace that we are happy to skip here.
    for child in expr.children() {
      match child.kind() {
        Syntax::Let => match self.desugar_let(child.clone()) {
          Ok((var, arg)) => binds.push((var, arg, child)),
          Err(error) => {
            let hole = self.hole(&child, error);
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
    self.hole(node, DesugarError::ExprMissingBody)
  }

  fn desugar_let(&mut self, bind: SyntaxNode<Lang>) -> Result<(String, Ast<String>), DesugarError> {
    let mut children = bind.children();

    let binder = children
      .next()
      .filter(|var| var.kind() == Syntax::LetBinder)
      .and_then(|var| var.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier))
      .ok_or(DesugarError::LetMissingBinding)?;

    let ast = match children.next()
        .filter(|expr| expr.kind() == Syntax::Expr) {
      Some(expr) => self.desugar_expr(expr),
      None => self.hole(&bind, DesugarError::LetMissingExpr),
    };

    Ok((binder.to_string(), ast))
  }

  fn desugar_fun(&mut self, fun: SyntaxNode<Lang>) -> Ast<String> {
    let mut children = fun.children();

    let Some(var) = children
      .next()
      .filter(|var| var.kind() == Syntax::FunBinder)
      .and_then(|node| node.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier))
    else {
      return self.hole(&fun, DesugarError::FunMissingBinding);
    };

    let body = match children.next().filter(|expr| expr.kind() == Syntax::Expr) {
      Some(expr) => self.desugar_expr(expr),
      None => self.hole(&fun, DesugarError::FunMissingExpr),
    };

    let id = self.next_id();
    self.insert_node(id, SyntaxNodePtr::new(&fun));
    Ast::fun(id, var.to_string(), body)
  }

  fn desugar_app(&mut self, app: SyntaxNode<Lang>) -> Ast<String> {
    // Handle the case where our application is a single expression, rather than a function and
    // argument.
    let Syntax::App = app.kind() else {
      return self.desugar_atom(app);
    };

    let mut children = app.children();

    let fun = match children.next() {
      Some(fun) => self.desugar_app(fun),
      None => self.hole(&app, DesugarError::ApplicationMissingFun),
    };

    let arg = match children.next() {
      Some(arg) => self.desugar_atom(arg),
      None => self.hole(&app, DesugarError::ApplicationMissingArg),
    };

    let id = self.next_id();
    self.insert_node(id, SyntaxNodePtr::new(&app));
    Ast::app(id, fun, arg)
  }

  fn desugar_atom(&mut self, atom: SyntaxNode<Lang>) -> Ast<String> {
    match atom.kind() {
      Syntax::Var => {
        let Some(var) = atom.first_child_or_token_by_kind(&|kind| kind == Syntax::Identifier)
        else {
          return self.hole(&atom, DesugarError::VarMissingIdentifier);
        };
        let id = self.next_id();
        self.insert_node(id, SyntaxNodePtr::new(&atom));
        Ast::Var(id, var.to_string())
      }
      Syntax::IntegerExpr => {
        let Some(int) = atom.first_child_or_token_by_kind(&|kind| kind == Syntax::Int) else {
          return self.hole(&atom, DesugarError::IntegerExprMissingInt);
        };

        let val = match int.to_string().parse() {
          Ok(int) => int,
          Err(err) => return self.hole(&atom, DesugarError::InvalidInt(err)),
        };
        let id = self.next_id();
        self.insert_node(id, SyntaxNodePtr::new(&atom));
        Ast::Int(id, val)
      }
      Syntax::ParenthesizedExpr => match atom.first_child_by_kind(&|kind| kind == Syntax::Expr) {
        Some(expr) => self.desugar_expr(expr),
        None => self.hole(&atom, DesugarError::MissingSyntax(Syntax::Expr)),
      },
      Syntax::Fun => self.desugar_fun(atom),
      _ => self.hole(&atom, DesugarError::UnexpectedAtom(atom.kind())),
    }
  }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct SyntaxNodeHandle {
  pub root: GreenNode,
  pub ptr: SyntaxNodePtr<Lang>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DesugarOut {
  pub ast: Ast<String>,
  pub ast_to_cst: HashMap<NodeId, SyntaxNodeHandle>,
  pub errors: HashMap<SyntaxNodePtr<Lang>, DesugarError>,
}

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
let x = |a| a;
let y = |
  b | x b;
y (
  | c | c
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
        ),
      )
    );
  }
}
