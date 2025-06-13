use std::collections::HashMap;
use std::ops::Range;
use std::sync::atomic::{AtomicUsize, Ordering};

use dashmap::DashMap;
use desugar_base::{DesugarError, ErrorKind, SyncNode};
use name_resolution_base::NameResolutionError;
use parser_base::{Cst, ParseError};
use tower_lsp_server::lsp_types::{Diagnostic, Position, Range as LspRange, Uri};
use types_base::{Ast, NodeId, TypeError, TypeErrorKind, TypeScheme, TypedVar, Var};
use wasm_bindgen::JsValue;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Color {
  Red,
  Green,
}

#[derive(Default, Debug)]
struct ColorMap {
  storage: DashMap<QueryKey, (Color, usize)>,
}
impl ColorMap {
  fn get(&self, key: &QueryKey) -> Option<(Color, usize)> {
    self.storage.get(key).map(|r| *r.value())
  }

  fn mark_red(&self, key: QueryKey, revision: usize) -> Option<(Color, usize)> {
    self.storage.insert(key, (Color::Red, revision))
  }

  fn mark_green(&self, key: QueryKey, reivision: usize) -> Option<(Color, usize)> {
    self.storage.insert(key, (Color::Green, reivision))
  }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum QueryKey {
  ContentOf(Uri),
  CstOf(Uri),
  NewlinesOf(Uri),
  DesugarOf(Uri),
  NameresolveOf(Uri),
  TypesOf(Uri),
}

#[derive(Default, Debug)]
pub struct Database {
  colors: ColorMap,
  // Query caches
  content_input: DashMap<QueryKey, String>,
  cst_query: DashMap<QueryKey, (Cst, Vec<ParseError>)>,
  newlines_query: DashMap<QueryKey, Newlines>,
  desugar_query: DashMap<QueryKey, Result<(Ast<String>, HashMap<NodeId, SyncNode>), PellucidError>>,
  nameresolve_query: DashMap<QueryKey, Result<Ast<Var>, PellucidError>>,
  types_query: DashMap<QueryKey, Result<(Ast<TypedVar>, TypeScheme), PellucidError>>,
  revision: AtomicUsize,
}

#[derive(Default, Clone, PartialEq, Eq, Debug)]
pub struct Newlines {
  /// Each index of our vector is a line in our file.
  /// The value stored at each index is the byte offset where that line starts.
  line_offsets: Vec<usize>,
  /// Length of the string in bytes.
  len: usize,
}

impl Newlines {
  fn new(content: &str) -> Self {
    let mut byte = 0;
    let mut line_offsets = vec![];
    for line in content.lines() {
      line_offsets.push(byte);
      // Include 1 character for the newline itself
      byte += line.len() + 1;
    }
    // Push our final line.
    //line_offsets.push(byte);
    Self {
      line_offsets,
      len: content.len(),
    }
  }

  fn linecol_of(&self, byte: usize) -> Option<(u32, u32)> {
    if byte > self.len {
      return None;
    }
    let line = self.line_offsets.partition_point(|&offset| offset <= byte) - 1;
    let start = self.line_offsets[line];
    let col = byte - start;
    Some((line.try_into().unwrap(), col.try_into().unwrap()))
  }

  fn byte_of(&self, line: u32, character: u32) -> Option<usize> {
    self
      .line_offsets
      .get(line as usize)
      .map(|start| start + (character as usize))
  }

  fn lsp_range_for(&self, range: Range<usize>) -> Option<LspRange> {
    let (start_line, start_col) = self.linecol_of(range.start)?;
    let (end_line, end_col) = self.linecol_of(range.end)?;
    Some(LspRange {
      start: Position::new(start_line, start_col),
      end: Position::new(end_line, end_col),
    })
  }

  pub fn byte_range_for(&self, range: LspRange) -> Option<Range<usize>> {
    let start = self.byte_of(range.start.line, range.start.character)?;
    let end = self.byte_of(range.end.line, range.end.character)?;
    Some(start..end)
  }
}

// Implementation details
impl Database {
  fn dependencies(&self, key: &QueryKey) -> Vec<QueryKey> {
    match key {
      QueryKey::ContentOf(_) => vec![],
      QueryKey::CstOf(uri) => vec![QueryKey::ContentOf(uri.clone())],
      QueryKey::NewlinesOf(uri) => vec![QueryKey::ContentOf(uri.clone())],
      QueryKey::DesugarOf(uri) => vec![
        QueryKey::CstOf(uri.clone()),
        QueryKey::NewlinesOf(uri.clone()),
      ],
      QueryKey::NameresolveOf(uri) => vec![QueryKey::DesugarOf(uri.clone())],
      QueryKey::TypesOf(uri) => vec![QueryKey::NameresolveOf(uri.clone())],
    }
  }

  fn run_query(&self, key: QueryKey) {
    match key {
      QueryKey::ContentOf(_) => { /* this is input query, so running it does nothing. */ }
      QueryKey::CstOf(uri) => {
        self.cst_of(uri);
      }
      QueryKey::NewlinesOf(uri) => {
        self.newlines_of(uri);
      }
      QueryKey::DesugarOf(uri) => {
        let _ = self.desugar_of(uri);
      }
      QueryKey::NameresolveOf(uri) => {
        let _ = self.nameresolve_of(uri);
      }
      QueryKey::TypesOf(uri) => {
        let _ = self.types_of(uri);
      }
    }
  }

  fn try_mark_green(&self, key: QueryKey) -> Color {
    let revision = self.revision.load(Ordering::SeqCst);
    for dep in self.dependencies(&key) {
      match self.colors.get(&key) {
        Some((Color::Green, rev)) if revision == rev => continue,
        Some((Color::Red, _)) => return Color::Red,
        _ => {
          if self.try_mark_green(dep.clone()) != Color::Green {
            self.run_query(dep);
            // Because we just ran the query we can be sure the revision is up to date.
            match self.colors.get(&key) {
              Some((Color::Green, _)) => continue,
              Some((Color::Red, _)) => return Color::Red,
              None => unreachable!(),
            }
          }
        }
      }
    }
    // if we marked all dependencies green, mark this node green
    self.colors.mark_green(key, revision);
    Color::Green
  }

  fn query<V: PartialEq + Clone>(
    &self,
    key: QueryKey,
    cache: &DashMap<QueryKey, V>,
    producer: impl FnOnce(&Self, &QueryKey) -> V,
  ) -> V {
    let Some((_, rev)) = self.colors.get(&key) else {
      // We have not yet run this query, so we must run it.
      let value = producer(self, &key);
      cache.insert(key.clone(), value.clone());
      self
        .colors
        .mark_red(key, self.revision.load(Ordering::SeqCst));
      return value;
    };
    let revision = self.revision.load(Ordering::SeqCst);
    let update_value = |key| {
      let value = producer(self, &key);
      let old = cache.insert(key.clone(), value.clone());
      match old {
        Some(old) if old == value => self.colors.mark_green(key, revision),
        _ => self.colors.mark_red(key, revision),
      };
      value
    };
    // Our query is outdated
    if rev < revision {
      return update_value(key);
    }

    let color = self.try_mark_green(key.clone());
    match color {
      Color::Green => cache
        .get(&key)
        .unwrap_or_else(|| {
          panic!(
            "Green query {:?} missing value in cache\n{:?}",
            key, self.colors
          )
        })
        .value()
        .clone(),
      Color::Red => update_value(key),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PellucidError {
  Parser(Vec<ParseError>),
  Desugar(DesugarError),
  Nameres(NameResolutionError),
  Types(TypeError),
}

// Public queries
impl Database {
  pub fn set_input(&self, uri: Uri, content: String) {
    let key = QueryKey::ContentOf(uri);
    self.content_input.insert(key.clone(), content);
    let old_revision = self.revision.fetch_add(1, Ordering::SeqCst);
    self.colors.mark_red(key, old_revision + 1);
  }

  pub fn content_of(&self, uri: Uri) -> String {
    self.colors.mark_green(
      QueryKey::ContentOf(uri.clone()),
      self.revision.load(Ordering::SeqCst),
    );
    self
      .content_input
      .get(&QueryKey::ContentOf(uri))
      .map(|r| r.value().clone())
      .expect("Uri was queried with unset value")
  }

  pub fn cst_of(&self, uri: Uri) -> (parser_base::Cst, Vec<ParseError>) {
    self.query(QueryKey::CstOf(uri), &self.cst_query, |this, key| {
      let QueryKey::CstOf(uri) = key else {
        unreachable!()
      };
      let content = this.content_of(uri.clone());
      parser_base::parse(&content)
    })
  }

  pub fn newlines_of(&self, uri: Uri) -> Newlines {
    self.query(
      QueryKey::NewlinesOf(uri),
      &self.newlines_query,
      |this, key| {
        let QueryKey::NewlinesOf(uri) = key else {
          unreachable!()
        };
        let content = this.content_of(uri.clone());
        Newlines::new(&content)
      },
    )
  }

  pub fn desugar_of(
    &self,
    uri: Uri,
  ) -> Result<(Ast<String>, HashMap<NodeId, SyncNode>), PellucidError> {
    self.query(
      QueryKey::DesugarOf(uri),
      &self.desugar_query,
      |this, key| {
        let QueryKey::DesugarOf(uri) = key else {
          unreachable!()
        };
        let (cst, errors) = this.cst_of(uri.clone());
        if !errors.is_empty() {
          return Err(PellucidError::Parser(errors));
        }
        desugar_base::desugar(cst).map_err(PellucidError::Desugar)
      },
    )
  }

  pub fn nameresolve_of(&self, uri: Uri) -> Result<Ast<Var>, PellucidError> {
    self.query(
      QueryKey::NameresolveOf(uri),
      &self.nameresolve_query,
      |this, key| {
        let QueryKey::NameresolveOf(uri) = key else {
          unreachable!()
        };
        let (ast, _) = this.desugar_of(uri.clone())?;
        name_resolution_base::name_resolution(ast).map_err(PellucidError::Nameres)
      },
    )
  }

  pub fn types_of(&self, uri: Uri) -> Result<(Ast<TypedVar>, TypeScheme), PellucidError> {
    self.query(
      QueryKey::TypesOf(uri.clone()),
      &self.types_query,
      |this, key| {
        let QueryKey::TypesOf(uri) = key else {
          unreachable!()
        };
        let resolved_ast = this.nameresolve_of(uri.clone())?;
        types_base::type_infer(resolved_ast).map_err(PellucidError::Types)
      },
    )
  }

  pub fn diagnostics(&self, uri: Uri) -> Vec<Diagnostic> {
    // TODO: We should produce multiple diagnostics here.
    match self.types_of(uri.clone()) {
      Ok(_) => {
        vec![]
      }
      Err(err) => {
        let newlines = self.newlines_of(uri.clone());

        match err {
          PellucidError::Parser(vec) => vec
            .into_iter()
            .map(|err| {
              Diagnostic::new_simple(
                newlines
                  .lsp_range_for(err.span)
                  .expect("error span outside range"),
                format!("Expected one of {:?}", err.expected),
              )
            })
            .collect(),
          PellucidError::Desugar(desugar) => {
            vec![Diagnostic::new_simple(
              newlines
                .lsp_range_for(desugar.span)
                .expect("error span outside range"),
              match desugar.kind {
                ErrorKind::MissingSyntax(node) => format!("Expected node {:?}", node),
                ErrorKind::ProgramMissingExpr => "Program missing expression node".to_string(),
                ErrorKind::ExpectedLetOrAppInExpr(syntax) => {
                  format!("Expected let or app node, but encountered {:?}", syntax)
                }
                ErrorKind::LetMissingBinding => "Let missing a variable".to_string(),
                ErrorKind::LetMissingExpr => "Let missing a rhs expr".to_string(),
                ErrorKind::Unexpected(vec) => format!("Unexpected {:?}", vec), //TODO: Format this
                //better
                ErrorKind::InvalidInt(_) => "Expected an integer".to_string(),
                ErrorKind::FunMissingIdentifier => "Function missing a variable".to_string(),
                ErrorKind::FunMissingExpr => "Function missing a body".to_string(),
                ErrorKind::EmptyApplication => "Expected application but it was empty".to_string(),
                ErrorKind::VarMissingIdentifier => {
                  "Expected variable to contain an identifier token".to_string()
                }
                ErrorKind::IntegerExprMissingInt => {
                  "Expected integer expr to contain an int token".to_string()
                }
              },
            )]
          }
          PellucidError::Nameres(nameres) => {
            let (_, ast_to_cst) = self
              .desugar_of(uri)
              .expect("We can be sure this is Ok(_) otherwise we'd hit DesugarError case above");

            let (node_id, var) = match nameres {
              NameResolutionError::UndefinedVar(node_id, var) => (node_id, var),
            };
            vec![Diagnostic::new_simple(
              newlines
                .lsp_range_for(ast_to_cst[&node_id].span.into())
                .expect("error span outside range"),
              format!("Undefined variable {}", var),
            )]
          }
          PellucidError::Types(types) => {
            let (ast, ast_to_cst) = self
              .desugar_of(uri.clone())
              .expect("We can be sure this is Ok(_) otherwise we'd hit DesugarError case above");
            web_sys::console::log_1(&JsValue::from_str(&format!("{:?}", self.colors)));
            vec![Diagnostic::new_simple(
              newlines
                .lsp_range_for(ast_to_cst[&types.node_id].span.into())
                .expect("error span outside range"),
              match types.kind {
                TypeErrorKind::TypeNotEqual(left, right) => {
                  let node = ast
                    .find(types.node_id)
                    .expect("Node id is missing an AST node");
                  match node {
                    Ast::Var(node_id, _) => todo!(),
                    Ast::Int(node_id, _) => todo!(),
                    Ast::Fun(node_id, _, ast) => todo!(),
                    Ast::App(node_id, ast, ast1) => todo!(),
                  }
                  format!("Types are not equal: {:?} != {:?}", left, right)
                }
                TypeErrorKind::InfiniteType(type_var, ty) => format!(
                  "Tried to solve variable {:?} to infinite type {:?}",
                  type_var, ty
                ),
              },
            )]
          }
        }
      }
    }
  }
}

trait Find {
  fn find(&self, id: NodeId) -> Option<&Self>;
}
impl<T> Find for Ast<T> {
  fn find(&self, id: NodeId) -> Option<&Ast<T>> {
    match self {
      Ast::Var(node_id, _) => (node_id == &id).then_some(self),
      Ast::Int(node_id, _) => (node_id == &id).then_some(self),
      Ast::Fun(node_id, _, body) => {
        if node_id == &id {
          return Some(self);
        }
        body.find(id)
      }
      Ast::App(node_id, fun, arg) => {
        if node_id == &id {
          return Some(self);
        }
        fun.find(id).or_else(|| arg.find(id))
      }
    }
  }
}
