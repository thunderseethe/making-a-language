use types_base::{Ast, Var};

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

#[derive(Debug, PartialEq, Eq)]
pub enum NameResolutionError {
  UndefinedVar(String),
}

fn resolve(
  supply: &mut VarSupply,
  ast: Ast<String>,
  env: im::HashMap<String, Var>,
) -> Result<Ast<Var>, NameResolutionError> {
  match ast {
    Ast::Var(v) => env
      .get(&v)
      .copied()
      .map(Ast::Var)
      .ok_or(NameResolutionError::UndefinedVar(v)),
    Ast::Int(i) => Ok(Ast::Int(i)),
    Ast::Fun(name, body) => {
      let var = supply.supply();
      let body = resolve(supply, *body, env.update(name, var))?;
      Ok(Ast::fun(var, body))
    }
    Ast::App(fun, arg) => {
      let fun = resolve(supply, *fun, env.clone())?;
      let arg = resolve(supply, *arg, env)?;
      Ok(Ast::app(fun, arg))
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
  use types_base::Ast;

  fn name_resolve(input: &str) -> Result<Ast<Var>, NameResolutionError> {
    let cst = parser_base::parse(input);
    let ast = desugar_base::desugar(input, cst).expect("Desugar to succeed");
    name_resolution(ast)
  }

  #[test]
  fn shadowing_works_as_expected() {
    let input = r#"
    let x = \x -> x;
    let y = \y -> x;
    let x = 3;
    y x"#;

    let ast = name_resolve(input);
    assert_eq!(
      ast,
      Ok(Ast::app(
        Ast::fun(
          Var(0),
          Ast::app(
            Ast::fun(
              Var(1),
              Ast::app(
                Ast::fun(Var(2), Ast::app(Ast::Var(Var(1)), Ast::Var(Var(2)))),
                Ast::Int(3)
              )
            ),
            Ast::fun(Var(3), Ast::Var(Var(0)))
          )
        ),
        Ast::fun(Var(4), Ast::Var(Var(4)))
      ))
    );
  }
}
