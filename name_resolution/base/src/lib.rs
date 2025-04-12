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

fn resolve(
  supply: &mut VarSupply,
  ast: Ast<String>,
  env: im::HashMap<String, Var>,
) -> Result<Ast<Var>, NameResolutionError> {
  match ast {
    Ast::Var(id, v) => env
      .get(&v)
      .copied()
      .map(|v| Ast::Var(id, v))
      .ok_or(NameResolutionError::UndefinedVar(id, v)),
    Ast::Int(id, i) => Ok(Ast::Int(id, i)),
    Ast::Fun(id, name, body) => {
      let var = supply.supply();
      let body = resolve(supply, *body, env.update(name, var))?;
      Ok(Ast::fun(id, var, body))
    }
    Ast::App(id, fun, arg) => {
      let fun = resolve(supply, *fun, env.clone())?;
      let arg = resolve(supply, *arg, env)?;
      Ok(Ast::app(id, fun, arg))
    }
  }
}

pub fn name_resolution(ast: Ast<String>) -> Result<Ast<Var>, NameResolutionError> {
  let mut supply = VarSupply::default();
  resolve(&mut supply, ast, im::HashMap::default())
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_base::builder::AstBuilder;
  use types_base::Ast;

  fn name_resolve(input: &str) -> Result<Ast<Var>, NameResolutionError> {
    let cst = parser_base::parse(input);
    let (ast, _) = desugar_base::desugar(input, cst)
        .expect("Desugar to succeed");
    name_resolution(ast)
  }

  #[test]
  fn shadowing_works_as_expected() {
    let input = r#"
    let x = \x -> x;
    let y = \y -> x;
    let x = 3;
    y x"#;

    let b = AstBuilder::default();
    let ast = name_resolve(input);
    assert_eq!(
      ast,
      Ok(b.locals(
        [
          (Var(0), b.fun(Var(4), b.var(Var(4)))),
          (Var(1), b.fun(Var(3), b.var(Var(0)))),
          (Var(2), b.int(3))
        ],
        b.app(b.var(Var(1)), b.var(Var(2))),
      ))
    );
  }
}
