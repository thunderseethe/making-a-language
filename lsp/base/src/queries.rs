use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Range;
use std::sync::{
  Arc,
  atomic::{AtomicUsize, Ordering},
};

use closure_convert_base::ItemId;
use dashmap::DashMap;
use desugar_base::{DesugarError, SyntaxNodeHandle};
use lowering_base::{IR, LowerOut};
use name_resolution_base::NameResolutionError;
use parser_base::{
  Cst, Lang, ParseError, Syntax,
  rowan::{NodeOrToken, SyntaxNode, SyntaxToken, TextSize, ast::SyntaxNodePtr},
};
use serde_json::json;
use tower_lsp_server::lsp_types::{
  CompletionItem, CompletionItemKind, CompletionResponse, Diagnostic, Hover, HoverContents, LSPAny,
  LanguageString, Location, MarkedString, Position, Range as LspRange, Uri,
};
use types_base::{Ast, NodeId, Type, TypeError, TypeScheme, TypedVar, Var};

use self::graph::DepGraph;
use self::prettyprint::{PrettyprintType, prettyprint_expected_syntax, prettyprint_ty};

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

pub(crate) mod graph {
  use dashmap::DashMap;
  use parking_lot::RwLock;
  use petgraph::graph::{DiGraph, NodeIndex};

  use super::QueryKey;

  #[derive(Default, Debug)]
  pub(crate) struct DepGraph {
    graph: RwLock<DiGraph<QueryKey, ()>>,
    indices: DashMap<QueryKey, NodeIndex>,
  }
  impl DepGraph {
    pub(crate) fn add_dependency(&self, from: QueryKey, to: QueryKey) {
      let mut graph = self.graph.write();
      let from_index = *self
        .indices
        .entry(from.clone())
        .or_insert_with(|| graph.add_node(from));
      let to_index = *self
        .indices
        .entry(to.clone())
        .or_insert_with(|| graph.add_node(to));
      graph.update_edge(from_index, to_index, ());
    }

    pub(crate) fn dependencies(&self, key: &QueryKey) -> Option<Vec<QueryKey>> {
      let index = self.indices.get(key)?;
      let graph = self.graph.read();
      let mut deps = graph.neighbors(*index).detach();
      let mut nodes = vec![];
      while let Some(node) = deps.next_node(&graph) {
        nodes.push(graph[node].clone());
      }
      Some(nodes)
    }
  }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub(crate) enum QueryKey {
  ContentOf(Uri),
  CstOf(Uri),
  NewlinesOf(Uri),
  DesugarOf(Uri),
  NameresolveOf(Uri),
  TypesOf(Uri),
  IrOf(Uri),
  SimpleIrOf(Uri),
  MonomorphOf(Uri),
  ClosureConvertOf(Uri),
  WasmOf(Uri),
  DiagnosticsOf(Uri),
  NodeStartingAt(Uri, Position),
  AstNodeOf(Uri, SyntaxNodeHandle),
  HoverOf(Uri, Position),
  ScopeOf(Uri, Position),
  CompletionOf(Uri, Position),
  DefinitionOf(Uri, Position),
  ReferencesOf(Uri, Position),
  ShowTreesOf(Uri),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DesugarOfResult {
  pub ast: Ast<String>,
  pub ast_to_cst: HashMap<NodeId, SyntaxNodeHandle>,
  pub errors: Vec<PellucidError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NameresOfResult {
  pub ast: Ast<Var>,
  pub names: HashMap<Var, String>,
  pub errors: Vec<PellucidError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypesOfResult {
  pub ast: Ast<TypedVar>,
  pub scheme: TypeScheme,
  pub errors: Vec<PellucidError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PellucidDesugarError {
  pub node: SyntaxNodeHandle,
  pub kind: desugar_base::DesugarError,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PellucidTypeError {
  pub node: NodeId,
  pub mark: TypeError,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PellucidNameResError {
  pub node: NodeId,
  pub kind: NameResolutionError,
}

#[derive(Default, Debug)]
pub struct Database {
  colors: ColorMap,
  revision: AtomicUsize,
  // Query caches
  content_input: DashMap<QueryKey, String>,
  cst_query: DashMap<QueryKey, (Cst, Vec<PellucidError>)>,
  newlines_query: DashMap<QueryKey, Newlines>,
  desugar_query: DashMap<QueryKey, DesugarOfResult>,
  nameresolve_query: DashMap<QueryKey, NameresOfResult>,
  types_query: DashMap<QueryKey, TypesOfResult>,
  ir_query: DashMap<QueryKey, Option<LowerOut>>,
  simple_ir_query: DashMap<QueryKey, Option<lowering_base::IR>>,
  monomorph_query: DashMap<QueryKey, Option<lowering_base::IR>>,
  closure_convert_query: DashMap<QueryKey, Option<closure_convert_base::ClosureConvertOutput>>,
  wasm_query: DashMap<QueryKey, Option<Vec<u8>>>,
  diagnostics_query: DashMap<QueryKey, Vec<Diagnostic>>,
  ast_node_query: DashMap<QueryKey, Option<Ast<TypedVar>>>,
  hover_query: DashMap<QueryKey, Option<Hover>>,
  node_starting_at_query: DashMap<QueryKey, Option<SyntaxNodeHandle>>,
  completion_query: DashMap<QueryKey, Option<CompletionResponse>>,
  definition_query: DashMap<QueryKey, Option<LspRange>>,
  reference_query: DashMap<QueryKey, Option<Vec<Location>>>,
  scope_query: DashMap<QueryKey, Option<HashMap<String, String>>>,
  show_trees_query: DashMap<QueryKey, LSPAny>,
}

impl Database {
  pub fn set_content(&self, uri: Uri, content: String) {
    let key = QueryKey::ContentOf(uri);
    self.content_input.insert(key.clone(), content);
    let old_revision = self.revision.fetch_add(1, Ordering::SeqCst);
    self.colors.mark_red(key, old_revision + 1);
  }
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
    Self {
      line_offsets,
      len: content.len(),
    }
  }

  fn linecol_of(&self, byte: usize) -> Option<(u32, u32)> {
    if byte > self.len {
      return None;
    }
    // We shouldn't need to special case this in theory, in practice however...
    if self.len == 0 {
      return Some((0, 0));
    }
    let line = self.line_offsets.partition_point(|&offset| offset <= byte) - 1;
    let start = self.line_offsets[line];
    let line: u32 = line.try_into().unwrap();
    let col = byte - start;
    let col: u32 = col.try_into().unwrap();
    Some((line, col))
  }

  fn byte_of(&self, line: u32, character: u32) -> Option<usize> {
    self
      .line_offsets
      .get((line) as usize)
      .map(|start| start + ((character) as usize))
  }

  pub fn lsp_range_for(&self, range: Range<usize>) -> Option<LspRange> {
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

pub(crate) struct QueryContext {
  parent: Option<QueryKey>,
  db: Arc<Database>,
  dep_graph: Arc<DepGraph>,
}
// Implementation details
impl QueryContext {
  pub(crate) fn with_root(db: Arc<Database>, dep_graph: Arc<DepGraph>) -> Self {
    Self {
      parent: None,
      db,
      dep_graph,
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
      QueryKey::AstNodeOf(uri, node) => {
        let _ = self.ast_node_of(uri, node);
      }
      QueryKey::HoverOf(uri, range) => {
        let _ = self.hover_of(uri, range);
      }
      QueryKey::NodeStartingAt(uri, cursor) => {
        let _ = self.syntax_node_starting_at(uri, cursor);
      }
      QueryKey::CompletionOf(uri, cursor) => {
        let _ = self.completion_of(uri, cursor);
      }
      QueryKey::DefinitionOf(uri, cursor) => {
        let _ = self.definition_of(uri, cursor);
      }
      QueryKey::ReferencesOf(uri, cursor) => {
        let _ = self.references_of(uri, cursor);
      }
      QueryKey::ScopeOf(uri, cursor) => {
        let _ = self.scope_at(uri, cursor);
      }
      QueryKey::ShowTreesOf(uri) => {
        let _ = self.show_trees_of(uri);
      }
      QueryKey::IrOf(uri) => {
        let _ = self.ir_of(uri);
      }
      QueryKey::SimpleIrOf(uri) => {
        let _ = self.simple_ir_of(uri);
      }
      QueryKey::MonomorphOf(uri) => {
        let _ = self.monomorph_of(uri);
      }
      QueryKey::ClosureConvertOf(uri) => {
        let _ = self.closure_convert_of(uri);
      }
      QueryKey::WasmOf(uri) => {
        let _ = self.wasm_of(uri);
      }
      QueryKey::DiagnosticsOf(uri) => {
        let _ = self.diagnostics_of(uri);
      }
    }
  }

  fn try_mark_green(&self, key: QueryKey) -> Color {
    let revision = self.db.revision.load(Ordering::SeqCst);
    // If we have no dependencies in the graph, assume we need to run the query.
    let Some(deps) = self.dep_graph.dependencies(&key) else {
      return Color::Red;
    };
    let Some((_, parent_rev)) = self.db.colors.get(&key) else {
      return Color::Red;
    };
    for dep in deps {
      match self.db.colors.get(&dep) {
        Some((Color::Green, rev)) if parent_rev >= rev => continue,
        Some((Color::Green, rev)) if parent_rev < rev => return Color::Red,
        Some((Color::Red, _)) => return Color::Red,
        color => {
          if self.try_mark_green(dep.clone()) != Color::Green {
            self.run_query(dep.clone());
            // Because we just ran the query we can be sure the revision is up to date.
            match self.db.colors.get(&dep) {
              Some((Color::Green, _)) => continue,
              Some((Color::Red, _)) => return Color::Red,
              None => unreachable!("color"),
            }
          }
        }
      }
    }
    // If we marked all dependencies green, mark this node green.
    self.db.colors.mark_green(key, revision);
    Color::Green
  }

  fn query<V: PartialEq + Clone>(
    &self,
    key: QueryKey,
    cache: &DashMap<QueryKey, V>,
    producer: impl FnOnce(&Self, &QueryKey) -> V,
  ) -> V {
    let revision = self.db.revision.load(Ordering::SeqCst);
    let update_value = |key: QueryKey| {
      if let Some(parent) = &self.parent {
        self.dep_graph.add_dependency(parent.clone(), key.clone());
      }
      let value = producer(
        &QueryContext {
          parent: Some(key.clone()),
          db: self.db.clone(),
          dep_graph: self.dep_graph.clone(),
        },
        &key,
      );
      let old = cache.insert(key.clone(), value.clone());
      if old.is_none_or(|old| old == value) {
        self.db.colors.mark_green(key, revision);
      } else {
        self.db.colors.mark_red(key, revision);
      }
      value
    };
    let color = self.try_mark_green(key.clone());
    match color {
      Color::Green => cache
        .get(&key)
        .unwrap_or_else(|| {
          panic!(
            "Green query {:?} missing value in cache\n{:?}",
            key, self.db.colors
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
  Parser(ParseError),
  Desugar(PellucidDesugarError),
  Nameres(PellucidNameResError),
  Types(PellucidTypeError),
}

// Public queries
impl QueryContext {
  pub fn content_of(&self, uri: Uri) -> String {
    let key = QueryKey::ContentOf(uri.clone());
    if let Some(parent) = &self.parent {
      self.dep_graph.add_dependency(parent.clone(), key.clone());
    }
    self
      .db
      .colors
      .mark_green(key, self.db.revision.load(Ordering::SeqCst));
    self
      .db
      .content_input
      .get(&QueryKey::ContentOf(uri))
      .map(|r| r.value().clone())
      .expect("Uri was queried with unset value")
  }

  pub fn cst_of(&self, uri: Uri) -> (parser_base::Cst, Vec<PellucidError>) {
    self.query(QueryKey::CstOf(uri), &self.db.cst_query, |this, key| {
      let QueryKey::CstOf(uri) = key else {
        unreachable!("cst")
      };
      let content = this.content_of(uri.clone());
      let (root, errors) = parser_base::parse(&content);
      (
        root,
        errors.into_iter().map(PellucidError::Parser).collect(),
      )
    })
  }

  pub fn newlines_of(&self, uri: Uri) -> Newlines {
    self.query(
      QueryKey::NewlinesOf(uri),
      &self.db.newlines_query,
      |this, key| {
        let QueryKey::NewlinesOf(uri) = key else {
          unreachable!("newlines")
        };
        let content = this.content_of(uri.clone());
        Newlines::new(&content)
      },
    )
  }

  pub fn desugar_of(&self, uri: Uri) -> DesugarOfResult {
    self.query(
      QueryKey::DesugarOf(uri),
      &self.db.desugar_query,
      |this, key| {
        let QueryKey::DesugarOf(uri) = key else {
          unreachable!("desugar")
        };
        let (cst, _) = this.cst_of(uri.clone());
        let out = desugar_base::desugar(cst.clone());
        let errors = out
          .errors
          .into_iter()
          .map(|(ptr, kind)| {
            PellucidError::Desugar(PellucidDesugarError {
              kind,
              node: SyntaxNodeHandle {
                root: cst.clone(),
                ptr,
              },
            })
          })
          .collect();
        DesugarOfResult {
          ast: out.ast,
          ast_to_cst: out.ast_to_cst,
          errors,
        }
      },
    )
  }

  pub fn nameresolve_of(&self, uri: Uri) -> NameresOfResult {
    self.query(
      QueryKey::NameresolveOf(uri),
      &self.db.nameresolve_query,
      |this, key| {
        let QueryKey::NameresolveOf(uri) = key else {
          unreachable!("nameresolve")
        };
        let desugar = this.desugar_of(uri.clone());
        let nameres = name_resolution_base::name_resolution(desugar.ast);
        let errors = nameres
          .errors
          .into_iter()
          .map(|(node, kind)| PellucidError::Nameres(PellucidNameResError { node, kind }))
          .collect();
        NameresOfResult {
          ast: nameres.ast,
          names: nameres.names,
          errors,
        }
      },
    )
  }

  pub fn types_of(&self, uri: Uri) -> TypesOfResult {
    self.query(
      QueryKey::TypesOf(uri.clone()),
      &self.db.types_query,
      |this, key| {
        let QueryKey::TypesOf(uri) = key else {
          unreachable!("types")
        };
        let nameres = this.nameresolve_of(uri.clone());
        let out = types_base::type_infer(nameres.ast);
        let errors = out
          .errors
          .into_iter()
          .map(|(node, mark)| PellucidError::Types(PellucidTypeError { node, mark }))
          .collect();
        TypesOfResult {
          ast: out.ast,
          scheme: out.scheme,
          errors,
        }
      },
    )
  }

  pub fn ast_node_of(&self, uri: Uri, node: SyntaxNodeHandle) -> Option<Ast<TypedVar>> {
    self.query(
      QueryKey::AstNodeOf(uri.clone(), node),
      &self.db.ast_node_query,
      |this, key| {
        let QueryKey::AstNodeOf(uri, node) = key else {
          unreachable!("ast");
        };
        let desugar = this.desugar_of(uri.clone());
        let id = desugar
          .ast_to_cst
          .iter()
          .find_map(|(id, sync_node)| (sync_node == node).then_some(id))?;

        let types = this.types_of(uri.clone());
        types.ast.find(*id).cloned()
      },
    )
  }

  pub fn definition_of(&self, uri: Uri, cursor: Position) -> Option<LspRange> {
    self.query(
      QueryKey::DefinitionOf(uri.clone(), cursor),
      &self.db.definition_query,
      |this, key| {
        let QueryKey::DefinitionOf(uri, cursor) = key else {
          unreachable!();
        };
        let syntax = this.syntax_node_starting_at(uri.clone(), cursor.clone())?;
        let ast_node = this.ast_node_of(uri.clone(), syntax)?;
        let Ast::Var(node_id, var) = ast_node else {
          return None;
        };
        let ast = this.nameresolve_of(uri.clone()).ast;
        let binder_id = ast
          .parents_of(node_id)?
          .into_iter()
          .find_map(|ast| match ast {
            Ast::Fun(node_id, bind, _) if bind == &var.0 => Some(node_id),
            _ => None,
          })?;
        let ast_to_cst = this.desugar_of(uri.clone()).ast_to_cst;
        let binder_node = ast_to_cst.get(binder_id)?;
        let root = SyntaxNode::new_root(binder_node.root.clone());
        let syntax = binder_node.ptr.to_node(&root);
        let mut binder = syntax;
        if binder.kind() == Syntax::Fun {
          binder = binder.first_child_by_kind(&|kind| kind == Syntax::FunBinder)?;
        }

        let range_node = binder.first_token()?;
        let newlines = this.newlines_of(uri.clone());
        let range = newlines.lsp_range_for(range_node.text_range().into())?;
        Some(range)
      },
    )
  }

  pub fn references_of(&self, uri: Uri, cursor: Position) -> Option<Vec<Location>> {
    self.query(
      QueryKey::ReferencesOf(uri.clone(), cursor),
      &self.db.reference_query,
      |this, key| {
        let QueryKey::ReferencesOf(uri, cursor) = key else {
          unreachable!()
        };
        let sync_node = this.syntax_node_starting_at(uri.clone(), cursor.clone())?;
        let ast_node = this.ast_node_of(uri.clone(), sync_node)?;
        let var = match ast_node {
          Ast::Var(_, var) | Ast::Fun(_, var, _) => var,
          _ => return None,
        };

        let ast = self.nameresolve_of(uri.clone()).ast;
        let vars = ast.var_reference(&var.0);

        let ast_to_cst = self.desugar_of(uri.clone()).ast_to_cst;
        let newlines = self.newlines_of(uri.clone());
        let references = vars
          .into_iter()
          .filter_map(|var| {
            let id = var.id();
            let sync_node = ast_to_cst.get(&id)?;
            let root = SyntaxNode::new_root(sync_node.root.clone());
            let mut syntax = sync_node.ptr.to_node(&root);
            if syntax.kind() == Syntax::Fun {
              syntax = syntax.first_child_by_kind(&|kind| kind == Syntax::FunBinder)?;
            }
            let token = syntax.first_token()?;
            let range = newlines.lsp_range_for(token.text_range().into())?;
            Some(Location {
              uri: uri.clone(),
              range,
            })
          })
          .collect();
        Some(references)
      },
    )
  }

  pub fn syntax_node_starting_at(&self, uri: Uri, cursor: Position) -> Option<SyntaxNodeHandle> {
    self.query(
      QueryKey::NodeStartingAt(uri, cursor),
      &self.db.node_starting_at_query,
      |this, key| {
        let QueryKey::NodeStartingAt(uri, cursor) = key else {
          unreachable!("starting")
        };
        let (green, _) = this.cst_of(uri.clone());
        let cst = SyntaxNode::<Lang>::new_root(green.clone());
        let newlines = this.newlines_of(uri.clone());
        let byte: u32 = newlines
          .byte_of(cursor.line, cursor.character)?
          .try_into()
          .unwrap();
        let token = cst.token_at_offset(TextSize::from(byte));
        let token = match token {
          parser_base::rowan::TokenAtOffset::None => return None,
          parser_base::rowan::TokenAtOffset::Single(token) => token,
          // Bias away from whitespace as it's unlikely to be what we want.
          // Bias towards identifiers, as they're more likely to be semantically interesting.
          // Othewrise choose the left one
          parser_base::rowan::TokenAtOffset::Between(left, right) => {
            match (left.kind(), right.kind()) {
              (_, Syntax::Whitespaces) | (Syntax::Identifier, _) => left,
              (Syntax::Whitespaces, _) | (_, Syntax::Identifier) => right,
              _ => left,
            }
          }
        };
        let node = token.parent()?;
        Some(SyntaxNodeHandle {
          root: green,
          ptr: SyntaxNodePtr::new(&node),
        })
      },
    )
  }

  pub fn hover_of(&self, uri: Uri, position: Position) -> Option<Hover> {
    self.query(
      QueryKey::HoverOf(uri, position),
      &self.db.hover_query,
      |this, key| {
        let QueryKey::HoverOf(uri, position) = key else {
          unreachable!("hover")
        };
        let cst = this.syntax_node_starting_at(uri.clone(), position.clone())?;
        let syntax = SyntaxNode::<Lang>::new_root(cst.root.clone());
        // We'll need this later to get the correct range for our hover, so we don't want to shadow
        // it.
        let cursor_node = cst.ptr.to_node(&syntax);

        // We only want to show a hover if our cursor is over a variable, either in expression or
        // bound position.
        let node = match cursor_node.kind() {
          Syntax::Var | Syntax::LetBinder => cursor_node.clone(),
          Syntax::FunBinder => cursor_node.parent()?,
          _ => return None,
        };

        let ast_node = this.ast_node_of(
          uri.clone(),
          SyntaxNodeHandle {
            root: cst.root.clone(),
            ptr: SyntaxNodePtr::new(&node),
          },
        )?;
        let ty = match &ast_node {
          Ast::Var(_, typed_var) => &typed_var.1,
          Ast::Fun(_, typed_var, _) => &typed_var.1,
          _ => return None,
        };
        let newlines = self.newlines_of(uri.clone());
        let range = newlines.lsp_range_for(cursor_node.text_range().into());
        Some(Hover {
          range,
          contents: HoverContents::Scalar(MarkedString::LanguageString(LanguageString {
            language: "pellucid".to_string(),
            value: prettyprint_ty(ty),
          })),
        })
      },
    )
  }

  pub fn scope_at(&self, uri: Uri, cursor: Position) -> Option<HashMap<String, String>> {
    self.query(
      QueryKey::ScopeOf(uri, cursor),
      &self.db.scope_query,
      |this, key| {
        let QueryKey::ScopeOf(uri, cursor) = key else {
          unreachable!()
        };

        let node = this.syntax_node_starting_at(uri.clone(), cursor.clone())?;

        let ast_node = this.ast_node_of(uri.clone(), node)?;

        let desugar = this.desugar_of(uri.clone());
        let types = this.types_of(uri.clone());
        let scoped_ast = zip_ast(desugar.ast, types.ast);
        let Some(parents) = scoped_ast.parents_of(ast_node.id()) else {
          return Some(HashMap::default());
        };

        // We reverse our iterator so that earlier entries in our parent list will overwrite later
        // entries, mirroring our scoping rules.
        let scope: HashMap<String, String> = parents
          .into_iter()
          .rev()
          .filter_map(|ast| match ast {
            Ast::Fun(_, (name, typed_var), _) => Some((name.clone(), prettyprint_ty(&typed_var.1))),
            _ => None,
          })
          .collect();
        Some(scope)
      },
    )
  }

  // Is it worth having a query for this?
  pub fn completion_of(&self, uri: Uri, cursor: Position) -> Option<CompletionResponse> {
    self.query(
      QueryKey::CompletionOf(uri, cursor),
      &self.db.completion_query,
      |this, key| {
        let QueryKey::CompletionOf(uri, cursor) = key else {
          unreachable!();
        };
        let scope = this
          .scope_at(uri.clone(), *cursor)?
          .into_iter()
          .collect::<Vec<_>>();

        Some(CompletionResponse::Array(
          scope
            .into_iter()
            .map(|(name, pretty_ty)| CompletionItem {
              label: name,
              kind: Some(CompletionItemKind::VARIABLE),
              detail: Some(pretty_ty),
              ..Default::default()
            })
            .collect(),
        ))
      },
    )
  }

  pub fn diagnostics_of(&self, uri: Uri) -> Vec<Diagnostic> {
    self.query(
      QueryKey::DiagnosticsOf(uri),
      &self.db.diagnostics_query,
      |this, key| {
        let QueryKey::DiagnosticsOf(uri) = key else {
          unreachable!()
        };
        let newlines = this.newlines_of(uri.clone());
        this
          .errors(uri.clone())
          .map(|err| match err {
            PellucidError::Parser(err) => Diagnostic::new_simple(
              newlines
                .lsp_range_for(err.span)
                .expect("error span outside range"),
              format!(
                "parse: Expected one of: {}",
                prettyprint_expected_syntax(&err.expected)
              ),
            ),
            PellucidError::Desugar(desugar) => Diagnostic::new_simple(
              newlines
                .lsp_range_for(desugar.node.ptr.text_range().into())
                .expect("error span outside range"),
              match desugar.kind {
                DesugarError::MissingSyntax(node) => format!("desugar: Expected node {node:?}"),
                DesugarError::LetMissingBinding => "desugar: Let missing a variable".to_string(),
                DesugarError::LetMissingExpr => "desugar: Let missing a rhs expr".to_string(),
                DesugarError::InvalidInt(_) => "desugar: Expected an integer".to_string(),
                DesugarError::FunMissingBinding => {
                  "desugar: Function missing a parameter".to_string()
                }
                DesugarError::FunMissingExpr => "desugar: Function missing a body".to_string(),
                DesugarError::VarMissingIdentifier => {
                  "desugar: Expected variable to contain an identifier token".to_string()
                }
                DesugarError::IntegerExprMissingInt => {
                  "desugar: Expected integer expr to contain an int token".to_string()
                }
                DesugarError::ApplicationMissingFun => {
                  "desugar: Application is missing a function".to_string()
                }
                DesugarError::ApplicationMissingArg => {
                  "desugar: Applicaiton is missing a argument".to_string()
                }
                DesugarError::ExprMissingBody => {
                  "desugar: Expected expression to have a body after let bindings.".to_string()
                }
                DesugarError::UnexpectedAtom(kind) => {
                  format!("desugar: Expecting an atom but found syntax {kind:?}.")
                }
              },
            ),
            PellucidError::Nameres(nameres) => {
              let desugar = this.desugar_of(uri.clone());
              let node_id = nameres.node;
              let var = match nameres.kind {
                NameResolutionError::UndefinedVar(_, var) => var,
              };
              Diagnostic::new_simple(
                newlines
                  .lsp_range_for(desugar.ast_to_cst[&node_id].ptr.text_range().into())
                  .expect("error span outside range"),
                format!("namres: Undefined variable {var}"),
              )
            }
            PellucidError::Types(types) => {
              let desugar = this.desugar_of(uri.clone());
              let range = newlines
                .lsp_range_for(desugar.ast_to_cst[&types.node].ptr.text_range().into())
                .expect("error span outside range");

              Diagnostic::new_simple(
                range,
                match types.mark {
                  TypeError::InfiniteType { type_var, ty } => format!(
                    "types: Tried to solve variable {} to infinite type {}",
                    prettyprint_ty(&Type::Var(type_var)),
                    prettyprint_ty(&ty)
                  ),
                  TypeError::UnexpectedFun {
                    expected_ty,
                    fun_ty,
                  } => format!(
                    "types: Expected a value of type {}, but found function of type {}",
                    prettyprint_ty(&expected_ty),
                    prettyprint_ty(&fun_ty)
                  ),
                  TypeError::AppExpectedFun {
                    inferred_ty,
                    expected_fun_ty,
                  } => format!(
                    "types: Expected this to be a function {} but it has type {}",
                    prettyprint_ty(&expected_fun_ty),
                    prettyprint_ty(&inferred_ty)
                  ),
                  TypeError::ExpectedUnify { checked, inferred } => format!(
                    "types: Tried to check this as type {} but it's inferred to have type {}",
                    prettyprint_ty(&checked),
                    prettyprint_ty(&inferred)
                  ),
                },
              )
            }
          })
          .collect()
      },
    )
  }

  pub fn errors(&self, uri: Uri) -> impl Iterator<Item = PellucidError> {
    let types = self.types_of(uri.clone());
    let nameres = self.nameresolve_of(uri.clone());
    let desugar = self.desugar_of(uri.clone());
    let (_, parse_errors) = self.cst_of(uri.clone());
    types
      .errors
      .into_iter()
      .chain(nameres.errors)
      .chain(desugar.errors)
      .chain(parse_errors)
  }

  pub fn ir_of(&self, uri: Uri) -> Option<LowerOut> {
    self.query(QueryKey::IrOf(uri), &self.db.ir_query, |this, key| {
      let QueryKey::IrOf(uri) = key else {
        unreachable!()
      };
      // If we have any errors, lowering will crash.
      // Exit early to avoid lowering invalid IR.
      for _ in this.errors(uri.clone()) {
        return None;
      }

      let types = this.types_of(uri.clone());
      let lower = lowering_base::lower(types.ast, types.scheme);

      Some(lower)
    })
  }

  pub fn simple_ir_of(&self, uri: Uri) -> Option<lowering_base::IR> {
    self.query(
      QueryKey::SimpleIrOf(uri),
      &self.db.simple_ir_query,
      |this, key| {
        let QueryKey::SimpleIrOf(uri) = key else {
          unreachable!()
        };
        let lower = this.ir_of(uri.clone())?;
        let simple_ir = simplify_base::simplify(lower.ir);

        Some(simple_ir)
      },
    )
  }

  pub fn monomorph_of(&self, uri: Uri) -> Option<lowering_base::IR> {
    self.query(
      QueryKey::MonomorphOf(uri.clone()),
      &self.db.monomorph_query,
      |this, _| {
        let ir = this.simple_ir_of(uri)?;
        Some(monomorph_base::trivial_monomorph(ir))
      },
    )
  }

  pub fn closure_convert_of(&self, uri: Uri) -> Option<closure_convert_base::ClosureConvertOutput> {
    self.query(
      QueryKey::ClosureConvertOf(uri.clone()),
      &self.db.closure_convert_query,
      |this, _| {
        let ir = this.monomorph_of(uri)?;
        Some(closure_convert_base::closure_convert(ir))
      },
    )
  }

  pub fn wasm_of(&self, uri: Uri) -> Option<Vec<u8>> {
    self.query(
      QueryKey::WasmOf(uri.clone()),
      &self.db.wasm_query,
      |this, _| {
        let nameres = this.nameresolve_of(uri.clone());
        let lower = this.ir_of(uri.clone())?;
        let closures = this.closure_convert_of(uri)?;

        let mut names: HashMap<closure_convert_base::VarId, String> = nameres
          .names
          .into_iter()
          .filter_map(|(ast_var, name)| {
            let ir_var = lower.vars.get(&ast_var)?;
            let closure_var = closures.vars.get(ir_var)?;
            Some((*closure_var, name))
          })
          .collect();

        let main_defn = ItemId(
          closures
            .closure_items
            .last_key_value()
            .map(|(key, _)| key.0 + 1)
            .unwrap_or(0),
        );
        let mut defns = closures.closure_items;
        let mut main_item = closures.item;
        // We're flagrantly cheating because we don't have real support for top level items.
        let main_var = closure_convert_base::VarId(usize::MAX);
        main_item.name = Some(closure_convert_base::Var {
          id: main_var,
          // This doesn't matter so we just make something up.
          ty: closure_convert_base::Type::Int,
        });
        names.insert(main_var, "main".to_string());
        defns.insert(main_defn, main_item);

        let module = emit_base::emit_wasm(defns.into_iter().collect(), names);
        Some(module)
      },
    )
  }
}

mod show_trees;

trait Find<T> {
  fn find(&self, id: NodeId) -> Option<&Self>;

  fn var_reference(&self, var: &T) -> Vec<&Self>;
}
impl<T: PartialEq> Find<T> for Ast<T> {
  fn find(&self, id: NodeId) -> Option<&Self> {
    match self {
      Ast::Var(node_id, _) | Ast::Hole(node_id, _) | Ast::Int(node_id, _) => {
        (node_id == &id).then_some(self)
      }
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

  fn var_reference(&self, needle: &T) -> Vec<&Self> {
    fn aux<'a, T: PartialEq>(ast: &'a Ast<T>, needle: &T, vec: &mut Vec<&'a Ast<T>>) {
      match ast {
        Ast::Var(_, var) => {
          if var == needle {
            vec.push(ast);
          }
        }
        Ast::Int(_, _) => {}
        Ast::Fun(_, var, body) => {
          if var == needle {
            vec.push(ast);
          }
          aux(body, needle, vec);
        }
        Ast::App(_, arg, fun) => {
          aux(arg, needle, vec);
          aux(fun, needle, vec);
        }
        Ast::Hole(_, _) => {}
      }
    }
    let mut vec = vec![];
    aux(self, needle, &mut vec);
    vec
  }
}

pub(crate) fn zip_ast(left: Ast<String>, right: Ast<TypedVar>) -> Ast<(String, TypedVar)> {
  match (left, right) {
    (Ast::Var(left_id, a), Ast::Var(right_id, b)) if left_id == right_id => {
      Ast::Var(left_id, (a, b))
    }
    // After desugaring, the only way we introdue a new hole is when we fail to resolve a
    // name, so we handle that case explicilty here.
    (Ast::Var(left_id, a), Ast::Hole(right_id, b)) if left_id == right_id => {
      Ast::Hole(left_id, (a, b))
    }
    (Ast::Int(left_id, a), Ast::Int(right_id, _)) if left_id == right_id => Ast::Int(left_id, a),
    (Ast::Fun(left_id, a_var, a_body), Ast::Fun(right_id, b_var, b_body))
      if left_id == right_id =>
    {
      let body = zip_ast(*a_body, *b_body);
      Ast::fun(left_id, (a_var, b_var), body)
    }
    (Ast::App(left_id, a_fun, a_arg), Ast::App(right_id, b_fun, b_arg)) if left_id == right_id => {
      let fun = zip_ast(*a_fun, *b_fun);
      let arg = zip_ast(*a_arg, *b_arg);
      Ast::app(left_id, fun, arg)
    }
    (Ast::Hole(left_id, a_hole), Ast::Hole(right_id, b_hole)) if left_id == right_id => {
      Ast::Hole(left_id, (a_hole, b_hole))
    }
    // Outside of our one case with Var, we should not see two different Ast nodes meet or
    // an Ast node meet a Hole, so we error if that does arise.
    (left, right) => unreachable!("{left:?} does not zip with {right:?}"),
  }
}

mod prettyprint {
  use std::collections::HashMap;

  use parser_base::Syntax;
  use pretty::{DocAllocator, DocBuilder, RcAllocator};
  use types_base::{Type, TypeVar};

  pub fn prettyprint_ty(ty: &Type) -> String {
    let mut pp = PrettyprintType::new();
    let doc = pp.pretty(ty, &RcAllocator);
    let mut out = String::new();
    doc.render_fmt(80, &mut out).unwrap();
    out
  }

  pub fn prettyprint_expected_syntax(expected: &[Syntax]) -> String {
    let expected: Vec<_> = expected.iter().copied().map(prettyprint_syntax).collect();
    expected.join(", ")
  }
  fn prettyprint_syntax(syntax: Syntax) -> &'static str {
    match syntax {
      Syntax::LeftParen => "(",
      Syntax::RightParen => ")",
      Syntax::VerticalBar => "|",
      Syntax::Equal => "=",
      Syntax::Semicolon => ";",
      Syntax::LetKw => "`let`",
      Syntax::Identifier => "an identifier",
      Syntax::Int => "an integer",
      Syntax::Whitespaces => "whitespace",
      Syntax::EndOfFile => "end of file",
      Syntax::Error => "error",
      Syntax::Fun => "a function",
      Syntax::FunBinder => "a function parameter",
      Syntax::App => "a function application",
      Syntax::ParenthesizedExpr => "a parenthesized expression",
      Syntax::Var => "a variable",
      Syntax::Let => "a let expression",
      Syntax::LetBinder => "a let binding",
      Syntax::Expr => "an expression",
      Syntax::IntegerExpr => "an integer",
      Syntax::Program => "a program",
    }
  }

  pub struct PrettyprintType {
    ty_var_names: Box<dyn Iterator<Item = String>>,
    ty_vars: HashMap<TypeVar, String>,
  }
  impl PrettyprintType {
    pub fn new() -> Self {
      Self {
        ty_var_names: Box::new(('\u{03B1}'..='\u{03D9}').map(|c| c.to_string())),
        ty_vars: HashMap::default(),
      }
    }

    pub fn prettyprint(&mut self, ty: &Type) -> String {
      let doc = self.pretty(ty, &RcAllocator);
      let mut out = String::new();
      doc.render_fmt(80, &mut out).unwrap();
      out
    }

    pub fn prettyprint_ir(&mut self, ty: &lowering_base::Type) -> String {
      let doc = self.pretty_ir(ty, &RcAllocator);
      let mut out = String::new();
      doc.render_fmt(80, &mut out).unwrap();
      out
    }

    fn pretty_var<'a>(
      &mut self,
      ty_var: TypeVar,
      a: &'a RcAllocator,
    ) -> DocBuilder<'a, RcAllocator> {
      a.text(
        self
          .ty_vars
          .entry(ty_var)
          .or_insert_with(|| {
            let Some(name) = self.ty_var_names.next() else {
              todo!("Error handling");
            };
            name
          })
          .clone(),
      )
    }

    fn pretty<'a>(&mut self, ty: &Type, a: &'a RcAllocator) -> DocBuilder<'a, RcAllocator> {
      fn requires_parens(ty: &Type) -> bool {
        matches!(ty, Type::Fun(_, _))
      }
      match ty {
        Type::Int => a.text("Int"),
        Type::Var(type_var) => self.pretty_var(*type_var, a),
        Type::Fun(arg_ty, ret_ty) => {
          let mut arg = self.pretty(arg_ty, a).clone();
          let ret = self.pretty(ret_ty, a).clone();
          if requires_parens(arg_ty) {
            arg = arg.parens();
          }
          arg
            .append(a.space().clone())
            .append("->")
            .append(a.space().clone())
            .append(ret)
        }
      }
    }

    fn pretty_ir<'a>(
      &mut self,
      ty: &lowering_base::Type,
      a: &'a RcAllocator,
    ) -> DocBuilder<'a, RcAllocator> {
      use lowering_base::{Kind, Type};
      match ty {
        Type::Int => a.text("Int"),
        Type::Var(type_var) => a.as_string(type_var),
        Type::Fun(arg_ty, ret_ty) => {
          let mut arg = self.pretty_ir(arg_ty, a);
          let ret = self.pretty_ir(ret_ty, a);
          if matches!(&**arg_ty, Type::Fun(_, _) | Type::TyFun(_, _)) {
            arg = arg.parens();
          }
          arg
            .append(a.space().clone())
            .append("->")
            .append(a.space().clone())
            .append(ret)
        }
        Type::TyFun(kind, ty) => {
          let kind_doc = match kind {
            Kind::Type => a.text("Type"),
          };
          kind_doc
            .append(a.space())
            .append(".")
            .append(a.space())
            .append(self.pretty_ir(ty, a))
        }
      }
    }
  }
}
