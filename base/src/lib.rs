#![allow(dead_code)]
use std::collections::HashSet;

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct Var(usize);

#[derive(PartialEq, Eq, Clone, Debug)]
struct TypedVar(Var, Type);

/// Our Abstract syntax tree
/// The lambda calculus + integer literals.
#[derive(Debug, PartialEq, Eq)]
enum Expr<V> {
    /// A local variable
    Var(V),
    /// An integer literal
    Int(isize),
    /// A function literal (lambda, closure).
    Fun(V, Box<Expr<V>>),
    /// Function application
    App(Box<Expr<V>>, Box<Expr<V>>),
}

impl<V> Expr<V> {
    fn fun(arg: V, body: Self) -> Self {
        Self::Fun(arg, Box::new(body))
    }

    fn app(fun: Self, arg: Self) -> Self {
        Self::App(Box::new(fun), Box::new(arg))
    }
}

/// Our type
/// Each AST node in our input will be annotated by a value of `Type`
/// after type inference succeeeds.
#[derive(PartialEq, Eq, Clone, Debug)]
enum Type {
    /// Type of integers
    Int,
    /// A type variable, stands for a value of Type
    Var(TypeVar),
    /// A function type
    Fun(Box<Self>, Box<Self>),
}
impl EqUnifyValue for Type {}
impl Type {
    fn fun(arg: Self, ret: Self) -> Self {
        Self::Fun(Box::new(arg), Box::new(ret))
    }

    fn occurs_check(&self, var: TypeVar) -> Result<(), Type> {
        match self {
            Type::Int => Ok(()),
            Type::Var(v) => if *v == var { Err(Type::Var(*v)) } else { Ok(()) },
            Type::Fun(arg, ret) => {
                arg.occurs_check(var).map_err(|_| self.clone())?;
                ret.occurs_check(var).map_err(|_| self.clone())
            },
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
struct TypeVar(u32);
impl UnifyKey for TypeVar {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TypeVar"
    }
}

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
enum Constraint {
    TypeEqual(Type, Type),
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
struct TypeInference {
    unification_table: InPlaceUnificationTable<TypeVar>,
}

struct GenOut {
    constraints: Vec<Constraint>,
    typed_ast: Expr<TypedVar>,
}

impl GenOut {
    fn new(constraints: Vec<Constraint>, typed_ast: Expr<TypedVar>) -> Self {
        Self {
            constraints,
            typed_ast,
        }
    }
}

/// Constraint generation
impl TypeInference {
    /// Create a unique type variable
    fn fresh_ty_var(&mut self) -> TypeVar {
        self.unification_table.new_key(None)
    }

    /// Infer type of `ast`
    /// Returns a list of constraints that need to be true and the type `ast` will have if
    /// constraints hold.
    fn infer(&mut self, env: im::HashMap<Var, Type>, ast: Expr<Var>) -> (GenOut, Type) {
        match ast {
            Expr::Int(i) => (GenOut::new(vec![], Expr::Int(i)), Type::Int),
            Expr::Var(v) => {
                let ty = &env[&v];
                (
                    GenOut::new(vec![], Expr::Var(TypedVar(v, ty.clone()))),
                    ty.clone(),
                )
            },
            Expr::Fun(arg, body) => {
                let arg_ty_var = self.fresh_ty_var();
                let env = env.update(arg, Type::Var(arg_ty_var));
                let (body_out, body_ty) = self.infer(env, *body);
                (
                    GenOut {
                        typed_ast: Expr::fun(
                            TypedVar(arg, Type::Var(arg_ty_var)),
                            body_out.typed_ast,
                        ),
                        ..body_out
                    },
                    Type::fun(Type::Var(arg_ty_var), body_ty),
                )
            }
            Expr::App(fun, arg) => {
                let (arg_out, arg_ty) = self.infer(env.clone(), *arg);

                let ret_ty = Type::Var(self.fresh_ty_var());
                let fun_ty = Type::fun(arg_ty, ret_ty.clone());

                let fun_out = self.check(env, *fun, fun_ty);

                (
                    GenOut::new(
                        arg_out
                            .constraints
                            .into_iter()
                            .chain(fun_out.constraints.into_iter())
                            .collect(),
                        Expr::app(fun_out.typed_ast, arg_out.typed_ast),
                    ),
                    ret_ty,
                )
            }
        }
    }

    fn check(&mut self, env: im::HashMap<Var, Type>, ast: Expr<Var>, ty: Type) -> GenOut {
        match (ast, ty) {
            (Expr::Int(i), Type::Int) => GenOut::new(vec![], Expr::Int(i)),
            (Expr::Fun(arg, body), Type::Fun(arg_ty, ret_ty)) => {
                let env = env.update(arg, *arg_ty);
                self.check(env, *body, *ret_ty)
            }
            (ast, expected_ty) => {
                let (mut out, actual_ty) = self.infer(env, ast);
                out.constraints
                    .push(Constraint::TypeEqual(expected_ty, actual_ty));
                out
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TypeError {
    TypeNotEqual(Type, Type),
    InfiniteType(TypeVar, Type),
}

fn occurs_check(var: TypeVar, ty: Type) -> Result<(), Type> {
    match &ty {
        Type::Int => Ok(()),
        Type::Var(v) => if *v == var { Err(Type::Var(*v)) } else { Ok(()) },
        Type::Fun(arg, ret) => {
            occurs_check(var, *arg.clone()).map_err(|_| ty.clone())?;
            occurs_check(var, *ret.clone()).map_err(|_| ty.clone())
        },
    }
}

/// Constraint solving
impl TypeInference {
    fn unification(&mut self, constraints: Vec<Constraint>) -> Result<(), TypeError> {
        for constr in constraints {
            match constr {
                Constraint::TypeEqual(left, right) => self.unify_ty_ty(left, right)?,
            }
        }
        Ok(())
    }

    fn normalize_ty(&mut self, ty: Type) -> Type {
        match ty {
            Type::Int => Type::Int,
            Type::Fun(arg, ret) => {
                let arg = self.normalize_ty(*arg);
                let ret = self.normalize_ty(*ret);
                Type::fun(arg, ret)
            }
            Type::Var(v) => match self.unification_table.probe_value(v) {
                Some(ty) => self.normalize_ty(ty),
                None => Type::Var(v),
            },
        }
    }

    fn unify_ty_ty(&mut self, unnorm_left: Type, unnorm_right: Type) -> Result<(), TypeError> {
        let left = self.normalize_ty(unnorm_left);
        let right = self.normalize_ty(unnorm_right);
        match (left, right) {
            (Type::Int, Type::Int) => Ok(()),
            (Type::Fun(a_arg, a_ret), Type::Fun(b_arg, b_ret)) => {
                self.unify_ty_ty(*a_arg, *b_arg)?;
                self.unify_ty_ty(*a_ret, *b_ret)
            }
            (Type::Var(a), Type::Var(b)) => {
                self.unification_table
                    .unify_var_var(a, b)
                    .map_err(|(l, r)| TypeError::TypeNotEqual(l, r))
            }
            (Type::Var(v), ty) | (ty, Type::Var(v)) => {
                ty.occurs_check(v)
                    .map_err(|ty| TypeError::InfiniteType(v, ty))?;
                self
                    .unification_table
                    .unify_var_value(v, Some(ty))
                    .map_err(|(l, r)| TypeError::TypeNotEqual(l, r))
            }
            (left, right) => Err(TypeError::TypeNotEqual(left, right)),
        }
    }
}

impl TypeInference {
    fn substitute(&mut self, ty: Type) -> (HashSet<TypeVar>, Type) {
        match ty {
            Type::Int => (HashSet::new(), Type::Int),
            Type::Var(v) => {
                let root = self.unification_table.find(v);
                match self.unification_table.probe_value(root) {
                    Some(ty) => self.substitute(ty),
                    None => {
                        let mut unbound = HashSet::new();
                        unbound.insert(root);
                        (unbound, Type::Var(root))
                    }
                }
            }
            Type::Fun(arg, ret) => {
                let (mut arg_unbound, arg) = self.substitute(*arg);
                let (ret_unbound, ret) = self.substitute(*ret);
                arg_unbound.extend(ret_unbound);
                (arg_unbound, Type::fun(arg, ret))
            }
        }
    }

    fn substitute_ast(&mut self, ast: Expr<TypedVar>) -> (HashSet<TypeVar>, Expr<TypedVar>) {
        match ast {
            Expr::Var(v) => {
                let (unbound, ty) = self.substitute(v.1);
                (unbound, Expr::Var(TypedVar(v.0, ty)))
            }
            Expr::Int(i) => (HashSet::new(), Expr::Int(i)),
            Expr::Fun(arg, body) => {
                let (mut unbound, ty) = self.substitute(arg.1);
                let arg = TypedVar(arg.0, ty);

                let (unbound_body, body) = self.substitute_ast(*body);
                unbound.extend(unbound_body);

                (unbound, Expr::fun(arg, body))
            }
            Expr::App(fun, arg) => {
                let (mut unbound_fun, fun) = self.substitute_ast(*fun);
                let (unbound_arg, arg) = self.substitute_ast(*arg);
                unbound_fun.extend(unbound_arg);
                (unbound_fun, Expr::app(fun, arg))
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct TypeScheme {
    unbound: HashSet<TypeVar>,
    ty: Type,
}

fn type_infer(ast: Expr<Var>) -> Result<(Expr<TypedVar>, TypeScheme), TypeError> {
    let mut ctx = TypeInference {
        unification_table: InPlaceUnificationTable::default(),
    };

    // Constraint generation
    let (out, ty) = ctx.infer(im::HashMap::default(), ast);

    // Constraint solving
    ctx.unification(out.constraints)?;

    // Apply our substition to our inferred types
    let (mut unbound, ty) = ctx.substitute(ty);
    let (unbound_ast, typed_ast) = ctx.substitute_ast(out.typed_ast);
    unbound.extend(unbound_ast);

    // Return our typed ast and it's type scheme
    Ok((typed_ast, TypeScheme { unbound, ty }))
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {

    use super::*;

    macro_rules! set {
        ($($ele:expr),*) => {{
            let mut tmp = HashSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

    #[test]
    fn infers_int() {
        let ast = Expr::Int(3);

        let ty_chk = type_infer(ast).expect("Type inference to succeed");
        assert_eq!(ty_chk.0, Expr::Int(3));
        assert_eq!(ty_chk.1.ty, Type::Int);
    }

    #[test]
    fn infers_id_fun() {
        let x = Var(0);
        let ast = Expr::fun(x, Expr::Var(x));

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(0);
        let typed_x = TypedVar(x, Type::Var(a));
        assert_eq!(ty_chk.0, Expr::fun(typed_x.clone(), Expr::Var(typed_x)));
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound: set![a],
                ty: Type::fun(Type::Var(a), Type::Var(a)),
            }
        )
    }

    #[test]
    fn infers_k_combinator() {
        let x = Var(0);
        let y = Var(1);
        let ast = Expr::fun(x, Expr::fun(y, Expr::Var(x)));

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(0);
        let b = TypeVar(1);
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound: set![a, b],
                ty: Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(a))),
            }
        );
    }

    #[test]
    fn infers_s_combinator() {
        let x = Var(0);
        let y = Var(1);
        let z = Var(2);
        let ast = Expr::fun(
            x,
            Expr::fun(
                y,
                Expr::fun(
                    z,
                    Expr::app(
                        Expr::app(Expr::Var(x), Expr::Var(z)),
                        Expr::app(Expr::Var(y), Expr::Var(z)),
                    ),
                ),
            ),
        );

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(2);
        let b = TypeVar(3);
        let c = TypeVar(4);
        let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
        let y_ty = Type::fun(Type::Var(a), Type::Var(b));
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound: set![a, b, c],
                ty: Type::fun(x_ty, Type::fun(y_ty, Type::fun(Type::Var(a), Type::Var(c)))),
            }
        )
    }

    #[test]
    fn type_infer_fails() {
        let x = Var(0);
        let ast = Expr::app(
            Expr::fun(x, Expr::app(Expr::Var(x), Expr::Int(3))),
            Expr::Int(1),
        );

        let ty_chk_res = type_infer(ast);

        assert_eq!(
            ty_chk_res,
            Err(TypeError::TypeNotEqual(
                Type::fun(Type::Int, Type::Var(TypeVar(1))),
                Type::Int
            ))
        );
    }
}
