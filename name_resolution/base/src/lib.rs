use types_base::{Ast, NodeId, Var};

#[derive(Default)]
struct VarSupply {
  next: usize,
}
impl VarSupply {
  fn supply(&mut self) -> Var {
    let id = self.next;
    self.next += 1;
    Var(id)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NameResolutionError {
  UndefinedVar(NodeId, String),
}

#[derive(Default)]
struct NameResolution {
  supply: VarSupply,
  names: std::collections::HashMap<Var, String>,
  errors: std::collections::HashMap<NodeId, NameResolutionError>,
}

impl NameResolution {
  fn resolve(&mut self, ast: Ast<String>, env: im::HashMap<String, Var>) -> Ast<Var> {
    match ast {
      Ast::Var(id, name) => match env.get(&name).copied() {
        Some(v) => Ast::Var(id, v),
        None => {
          self
            .errors
            .insert(id, NameResolutionError::UndefinedVar(id, name));
          let var = self.supply.supply();
          Ast::Hole(id, var)
        }
      },
      Ast::Int(id, i) => Ast::Int(id, i),
      Ast::Hole(id, _) => {
        let var = self.supply.supply();
        Ast::Hole(id, var)
      }
      Ast::Fun(id, name, body) => {
        let var = self.supply.supply();
        self.names.insert(var, name.clone());
        let body = self.resolve(*body, env.update(name, var));
        Ast::fun(id, var, body)
      }
      Ast::App(id, fun, arg) => {
        let fun = self.resolve(*fun, env.clone());
        let arg = self.resolve(*arg, env);
        Ast::app(id, fun, arg)
      }
    }
  }
}

pub struct NameResolutionOut {
  pub ast: Ast<Var>,
  pub errors: std::collections::HashMap<NodeId, NameResolutionError>,
  pub names: std::collections::HashMap<Var, String>,
}

pub fn name_resolution(ast: Ast<String>) -> NameResolutionOut {
  let mut nameres = NameResolution::default();
  let ast = nameres.resolve(ast, im::HashMap::default());
  NameResolutionOut {
    ast,
    errors: nameres.errors,
    names: nameres.names,
  }
}

#[cfg(test)]
mod tests {
  use std::collections::HashMap;

use super::*;
  use types_base::Ast;
  use types_base::builder::AstBuilder;

  fn name_resolve(input: &str) -> (Ast<Var>, HashMap<NodeId, NameResolutionError>) {
    let (cst, _) = parser_base::parse(input);
    let desugar = desugar_base::desugar(cst);
    let nameres = name_resolution(desugar.ast);
    (nameres.ast, nameres.errors)
  }

  #[test]
  fn shadowing_works_as_expected() {
    let input = r#"
    let x = \x -> x;
    let y = \y -> x;
    let x = 3;
    y x"#;

    let b = AstBuilder::default();
    let (ast, errors) = name_resolve(input);
    assert_eq!(
      ast,
      b.locals(
        [
          (Var(0), b.fun(Var(4), b.var(Var(4)))),
          (Var(1), b.fun(Var(3), b.var(Var(0)))),
          (Var(2), b.int(3))
        ],
        b.app(b.var(Var(1)), b.var(Var(2))),
      )
    );
    assert_eq!(errors, HashMap::default());
  }
}
