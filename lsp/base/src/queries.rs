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
use types_base::{Ast, TypeError, NodeId, Type, TypeScheme, TypedVar, Var};

use self::graph::DepGraph;
use self::prettyprint::{PrettyprintType, prettyprint_ty};

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
  AstNodeOf(Uri, SyntaxNodeHandle),
  HoverOf(Uri, SyntaxNodeHandle),
  NodeStartingAt(Uri, Position),
  ScopeOf(Uri, Position),
  CompletionOf(Uri, Position),
  DefinitionOf(Uri, Position),
  ReferenceOf(Uri, Position),
  ShowTreesOf(Uri),
  IrOf(Uri),
  SimpleIrOf(Uri),
  MonomorphOf(Uri),
  ClosureConvertOf(Uri),
  WasmOf(Uri),
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
  // Query caches
  content_input: DashMap<QueryKey, String>,
  cst_query: DashMap<QueryKey, (Cst, Vec<PellucidError>)>,
  newlines_query: DashMap<QueryKey, Newlines>,
  desugar_query: DashMap<QueryKey, DesugarOfResult>,
  nameresolve_query: DashMap<QueryKey, NameresOfResult>,
  types_query: DashMap<QueryKey, TypesOfResult>,
  ast_node_query: DashMap<QueryKey, Option<Ast<TypedVar>>>,
  hover_query: DashMap<QueryKey, Option<Hover>>,
  node_starting_at_query: DashMap<QueryKey, Option<SyntaxNodeHandle>>,
  completion_query: DashMap<QueryKey, Option<CompletionResponse>>,
  definition_query: DashMap<QueryKey, Option<LspRange>>,
  reference_query: DashMap<QueryKey, Option<Vec<Location>>>,
  scope_query: DashMap<QueryKey, Option<HashMap<String, String>>>,
  show_trees_query: DashMap<QueryKey, LSPAny>,
  ir_query: DashMap<QueryKey, Option<LowerOut>>,
  simple_ir_query: DashMap<QueryKey, Option<lowering_base::IR>>,
  monomorph_query: DashMap<QueryKey, Option<lowering_base::IR>>,
  closure_convert_query: DashMap<QueryKey, Option<closure_convert_base::ClosureConvertOutput>>,
  wasm_query: DashMap<QueryKey, Option<Vec<u8>>>,
  revision: AtomicUsize,
}

impl Database {
  pub fn set_input(&self, uri: Uri, content: String) {
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

  fn dependencies(&self, key: &QueryKey) -> Option<Vec<QueryKey>> {
    self.dep_graph.dependencies(key)
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
      QueryKey::ReferenceOf(uri, cursor) => {
        let _ = self.reference_at(uri, cursor);
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
    }
  }

  fn try_mark_green(&self, key: QueryKey) -> Color {
    let revision = self.db.revision.load(Ordering::SeqCst);
    // If we have no dependencies in the graph, assume we need to run the query.
    let Some(deps) = self.dependencies(&key) else {
      return Color::Red;
    };
    for dep in deps {
      match self.db.colors.get(&key) {
        Some((Color::Green, rev)) if revision == rev => continue,
        Some((Color::Red, _)) => return Color::Red,
        _ => {
          if self.try_mark_green(dep.clone()) != Color::Green {
            self.run_query(dep);
            // Because we just ran the query we can be sure the revision is up to date.
            match self.db.colors.get(&key) {
              Some((Color::Green, _)) => continue,
              Some((Color::Red, _)) => return Color::Red,
              None => unreachable!("color"),
            }
          }
        }
      }
    }
    // if we marked all dependencies green, mark this node green
    self.db.colors.mark_green(key, revision);
    Color::Green
  }

  fn query<V: PartialEq + Clone>(
    &self,
    key: QueryKey,
    cache: &DashMap<QueryKey, V>,
    producer: impl FnOnce(&Self, &QueryKey) -> V,
  ) -> V {
    let Some((_, rev)) = self.db.colors.get(&key) else {
      // We have not yet run this query, so we must run it.
      let value = producer(self, &key);
      cache.insert(key.clone(), value.clone());
      self
        .db
        .colors
        .mark_red(key, self.db.revision.load(Ordering::SeqCst));
      return value;
    };
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
      match old {
        Some(old) if old == value => self.db.colors.mark_green(key, revision),
        _ => self.db.colors.mark_red(key, revision),
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
    self.db.colors.mark_green(
      QueryKey::ContentOf(uri.clone()),
      self.db.revision.load(Ordering::SeqCst),
    );
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
        let (cst, mut errors) = this.cst_of(uri.clone());
        let out = desugar_base::desugar(cst.clone());
        errors.extend(out.errors.into_iter().map(|(ptr, kind)| {
          PellucidError::Desugar(PellucidDesugarError {
            kind,
            node: SyntaxNodeHandle {
              root: cst.clone(),
              ptr,
            },
          })
        }));
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
        let mut errors = desugar.errors;
        errors.extend(nameres.errors.into_iter().map(|(node, kind)| {
            PellucidError::Nameres(PellucidNameResError {
                node, kind
            })
        }));
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
        let mut errors = nameres.errors;
        errors.extend(
          out
            .errors
            .into_iter()
            .map(|(node, mark)| PellucidError::Types(PellucidTypeError { node, mark })),
        );
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
      |this, _key| {
        let syntax = this.syntax_node_starting_at(uri.clone(), cursor)?;
        let ast_node = this.ast_node_of(uri.clone(), syntax)?;
        let Ast::Var(node_id, var) = ast_node else {
          return None;
        };
        let ast_to_cst = this.desugar_of(uri.clone()).ast_to_cst;
        let ast = this.nameresolve_of(uri.clone()).ast;
        let binder_id = ast
          .parents_of(node_id)?
          .into_iter()
          .find_map(|ast| match ast {
            Ast::Fun(node_id, bind, _) if bind == &var.0 => Some(node_id),
            _ => None,
          })?;
        let binder_node = ast_to_cst.get(binder_id).or_else(|| {
          // If our variable is bound by a let and not a function we need the app node to get our
          // cst node.
          let parent = ast.parent_of(*binder_id)?;
          ast_to_cst.get(&parent.id())
        })?;
        let root = SyntaxNode::new_root(binder_node.root.clone());
        let syntax = binder_node.ptr.to_node(&root);
        let binder = syntax
          .first_child_by_kind(&|kind| kind == Syntax::FunBinder || kind == Syntax::LetBinder)?;
        let range_node = binder.first_token()?;

        let newlines = this.newlines_of(uri);

        let range = newlines.lsp_range_for(range_node.text_range().into())?;
        Some(range)
      },
    )
  }

  pub fn reference_at(&self, uri: Uri, cursor: Position) -> Option<Vec<Location>> {
    self.query(
      QueryKey::ReferenceOf(uri.clone(), cursor),
      &self.db.reference_query,
      |this, _| {
        let sync_node = this.syntax_node_starting_at(uri.clone(), cursor)?;
        let ast_node = this.ast_node_of(uri.clone(), sync_node)?;
        let var = match ast_node {
          Ast::Var(_, var) | Ast::Fun(_, var, _) => var,
          _ => return None,
        };
        let ast_to_cst = self.desugar_of(uri.clone()).ast_to_cst;
        let ast = self.nameresolve_of(uri.clone()).ast;

        let newlines = self.newlines_of(uri.clone());
        let vars = ast.var_reference(&var.0);
        Some(vars.into_iter().filter_map(|var| {
          let id = var.id();
          let sync_node = ast_to_cst.get(&id).or_else(|| {
            let Ast::Fun(_, _, _) = var else {
              return None;
            };
            let parent_id = ast.parent_of(id)?.id();
            ast_to_cst.get(&parent_id)
          })?;
          let root = SyntaxNode::new_root(sync_node.root.clone());
          let mut syntax = sync_node.ptr.to_node(&root);
          if [Syntax::Fun, Syntax::Let].contains(&syntax.kind()) {
            syntax = syntax.first_child_by_kind(&|kind| [Syntax::LetBinder, Syntax::FunBinder].contains(&kind))?;
          }
          let token = syntax.first_token()?;
          let range = newlines.lsp_range_for(token.text_range().into())?;
          Some(Location {
            uri: uri.clone(),
            range
          })
        }).collect())
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
            parser_base::rowan::TokenAtOffset::Between(left, right) => match (left.kind(), right.kind()) {
              (_, Syntax::Whitespaces) | (Syntax::Identifier, _) => left,
              (Syntax::Whitespaces, _) | (_, Syntax::Identifier) => right,
              _ => left
            },
        };
        let node = token.parent()?;
        Some(SyntaxNodeHandle {
          root: green,
          ptr: SyntaxNodePtr::new(&node),
        })
      },
    )
  }

  pub fn hover_of(&self, uri: Uri, node: SyntaxNodeHandle) -> Option<Hover> {
    self.query(
      QueryKey::HoverOf(uri, node),
      &self.db.hover_query,
      |this, key| {
        let QueryKey::HoverOf(uri, cst) = key else {
          unreachable!("hover")
        };
        let syntax = SyntaxNode::<Lang>::new_root(cst.root.clone());
        // We'll need this later to get the correct range for our hover, so we don't want to shadow
        // it.
        let cursor_node = cst.ptr.to_node(&syntax);

        // We only want to show a hover if our cursor is over a variable, either in expression or
        // bound position.
        let node = match cursor_node.kind() {
          Syntax::Var => cursor_node.clone(),
          Syntax::FunBinder => cursor_node.parent()?,
          Syntax::LetBinder => cursor_node.parent()?,
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
          // If we hover over a let binding, our ast node will be App(_, Fun(...), ...).
          Ast::App(_, fun, _) => match fun.as_ref() {
            Ast::Fun(_, typed_var, _) => &typed_var.1,
            _ => return None,
          },
          _ => return None,
        };
        let newlines = self.newlines_of(uri.clone());
        let range = newlines.lsp_range_for(cursor_node.text_range().into());
        Some(Hover {
          range,
          contents: HoverContents::Scalar(MarkedString::LanguageString(LanguageString {
            language: "haskell".to_string(),
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
        let desugar = this.desugar_of(uri.clone());
        let types = this.types_of(uri.clone());
        fn zip_ast(left: Ast<String>, right: Ast<TypedVar>) -> Ast<(String, TypedVar)> {
          match (left, right) {
            (Ast::Var(left_id, a), Ast::Var(right_id, b)) if left_id == right_id => {
              Ast::Var(left_id, (a, b))
            }
            // After desugaring, the only way we introdue a new hole is when we fail to resolve a
            // name, so we handle that case explicilty here.
            (Ast::Var(left_id, a), Ast::Hole(right_id, b)) if left_id == right_id => {
              Ast::Hole(left_id, (a, b))
            }
            (Ast::Int(left_id, a), Ast::Int(right_id, _)) if left_id == right_id => {
              Ast::Int(left_id, a)
            }
            (Ast::Fun(left_id, a_var, a_body), Ast::Fun(right_id, b_var, b_body))
              if left_id == right_id =>
            {
              let body = zip_ast(*a_body, *b_body);
              Ast::fun(left_id, (a_var, b_var), body)
            }
            (Ast::App(left_id, a_fun, a_arg), Ast::App(right_id, b_fun, b_arg))
              if left_id == right_id =>
            {
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
        let scoped_ast = zip_ast(desugar.ast, types.ast);
        let (root, _) = this.cst_of(uri.clone());
        let cst = SyntaxNode::<Lang>::new_root(root.clone());
        let newlines = this.newlines_of(uri.clone());

        let offset: u32 = newlines
          .byte_of(cursor.line, cursor.character)?
          .try_into()
          .unwrap();
        let token = cst.token_at_offset(offset.into()).left_biased()?;
        let node = token.parent()?;
        let ast_node = this.ast_node_of(
          uri.clone(),
          SyntaxNodeHandle {
            root,
            ptr: SyntaxNodePtr::new(&node),
          },
        )?;
        // TODO: Write this method.
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

        // TODO: We should add keywords here.
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

  pub fn diagnostics(&self, uri: Uri) -> Vec<Diagnostic> {
    // TODO: We should produce multiple diagnostics here.
    let types = self.types_of(uri.clone());
    if types.errors.is_empty() {
      return vec![];
    }
    let newlines = self.newlines_of(uri.clone());
    types
      .errors
      .into_iter()
      .map(|err| match err {
        PellucidError::Parser(err) => Diagnostic::new_simple(
          newlines
            .lsp_range_for(err.span)
            .expect("error span outside range"),
          format!("parse: Expected one of {:?}", err.expected),
        ),
        PellucidError::Desugar(desugar) => Diagnostic::new_simple(
          newlines
            .lsp_range_for(desugar.node.ptr.text_range().into())
            .expect("error span outside range"),
          match desugar.kind {
            DesugarError::MissingSyntax(node) => format!("Expected node {node:?}"),
            DesugarError::LetMissingBinding => "Let missing a variable".to_string(),
            DesugarError::LetMissingExpr => "Let missing a rhs expr".to_string(),
            DesugarError::InvalidInt(_) => "Expected an integer".to_string(),
            DesugarError::FunMissingBinding => "Function missing a parameter".to_string(),
            DesugarError::FunMissingExpr => "Function missing a body".to_string(),
            DesugarError::VarMissingIdentifier => {
              "Expected variable to contain an identifier token".to_string()
            }
            DesugarError::IntegerExprMissingInt => {
              "Expected integer expr to contain an int token".to_string()
            }
            DesugarError::ApplicationMissingFun => "Application is missing a function".to_string(),
            DesugarError::ApplicationMissingArg => "Applicaiton is missing a argument".to_string(),
            DesugarError::ExprMissingBody => {
              "Expected expression to have a body after let bindings.".to_string()
            }
            DesugarError::UnexpectedAtom(kind) => {
              format!("Expecting an atom but found syntax {kind:?}.")
            }
          },
        ),
        PellucidError::Nameres(nameres) => {
          let desugar = self.desugar_of(uri.clone());
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
          let desugar = self.desugar_of(uri.clone());
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
  }

  pub fn show_trees_of(&self, uri: Uri) -> LSPAny {
    self.query(
      QueryKey::ShowTreesOf(uri.clone()),
      &self.db.show_trees_query,
      |this, _| {
        let (green, _) = this.cst_of(uri.clone());
        let desugar = this.desugar_of(uri.clone());
        let types = this.types_of(uri.clone());

        let root = SyntaxNode::<Lang>::new_root(green);

        fn cst_to_json(nort: NodeOrToken<SyntaxNode<Lang>, SyntaxToken<Lang>>) -> LSPAny {
          let kind: u64 = nort.kind() as u64;
          let text_range: std::ops::Range<usize> = nort.text_range().into();
          json!({
            "key": kind,
            "text_range": {
              "start": text_range.start,
              "end": text_range.end
            },
            "children": if let NodeOrToken::Node(node) = nort {
              Some(node.children_with_tokens().map(cst_to_json).collect::<Vec<_>>())
            } else {
              None
            }
          })
        }

        fn zip_ast(left: Ast<String>, right: Ast<TypedVar>) -> Ast<(String, TypedVar)> {
          match (left, right) {
            (Ast::Var(left_id, a), Ast::Var(right_id, b)) if left_id == right_id => {
              Ast::Var(left_id, (a, b))
            }
            // After desugaring, the only way we introdue a new hole is when we fail to resolve a
            // name, so we handle that case explicilty here.
            (Ast::Var(left_id, a), Ast::Hole(right_id, b)) if left_id == right_id => {
              Ast::Hole(left_id, (a, b))
            }
            (Ast::Int(left_id, a), Ast::Int(right_id, _)) if left_id == right_id => {
              Ast::Int(left_id, a)
            }
            (Ast::Fun(left_id, a_var, a_body), Ast::Fun(right_id, b_var, b_body))
              if left_id == right_id =>
            {
              let body = zip_ast(*a_body, *b_body);
              Ast::fun(left_id, (a_var, b_var), body)
            }
            (Ast::App(left_id, a_fun, a_arg), Ast::App(right_id, b_fun, b_arg))
              if left_id == right_id =>
            {
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

        fn ast_to_json(printer: &mut PrettyprintType, ast: Ast<(String, TypedVar)>) -> LSPAny {
          match ast {
            Ast::Var(_, (name, ty)) => json!({
              "kind": "var",
              "name": name,
              "type": printer.prettyprint(&ty.1),
            }),
            Ast::Int(_, i) => json!({
              "kind": "int",
              "vallue": i
            }),
            Ast::Fun(_, (name, ty), body) => json!({
              "kind": "fun",
              "name": name,
              "type": printer.prettyprint(&ty.1),
              "body": ast_to_json(printer, *body)
            }),
            Ast::App(_, fun, arg) => json!({
              "kind": "app",
              "fun": ast_to_json(printer, *fun),
              "arg": ast_to_json(printer, *arg),
            }),
            Ast::Hole(_, (_, ty)) => json!({
              "kind": "hole",
              "type": printer.prettyprint(&ty.1)
            }),
          }
        }

        let ast = zip_ast(desugar.ast, types.ast);
        let mut printer = PrettyprintType::new();
        let ast_json = ast_to_json(&mut printer, ast);

        let cst_json = cst_to_json(NodeOrToken::Node(root));

        fn ir_to_json(
          printer: &mut PrettyprintType,
          names: &HashMap<lowering_base::VarId, String>,
          ir: lowering_base::IR,
        ) -> LSPAny {
          let var_name = |var_id| {
            if let Some(name) = names.get(var_id) {
              name.clone()
            } else {
              format!("{var_id}")
            }
          };
          match ir {
            IR::Var(var) => json!({
              "kind": "var",
              "name": var_name(&var.id),
              "type": printer.prettyprint_ir(&var.ty),
            }),
            IR::Int(i) => json!({
              "kind": "int",
              "value": i,
            }),
            IR::Fun(var, ir) => json!({
              "kind": "fun",
              "name": var_name(&var.id),
              "type": printer.prettyprint_ir(&var.ty),
              "body": ir_to_json(printer, names, *ir),
            }),
            IR::App(fun, arg) => json!({
              "kind": "app",
              "fun": ir_to_json(printer, names, *fun),
              "arg": ir_to_json(printer, names, *arg),
            }),
            IR::TyFun(kind, ir) => json!({
              "kind": "ty_fun",
              "ty_fun_kind": format!("{:?}", kind),
              "body": ir_to_json(printer, names, *ir)
            }),
            IR::TyApp(ir, ty) => json!({
              "kind": "ty_app",
              "ty_fun": ir_to_json(printer, names, *ir),
              "type": printer.prettyprint_ir(&ty),
            }),
            IR::Local(var, defn, body) => json!({
              "kind": "local",
              "name": var_name(&var.id),
              "type": printer.prettyprint_ir(&var.ty),
              "defn": ir_to_json(printer, names, *defn),
              "body": ir_to_json(printer, names, *body),
            }),
          }
        }

        let names = this.nameresolve_of(uri.clone()).names;
        let ir_vars = this
          .ir_of(uri.clone())
          .map(|ir| ir.vars)
          .unwrap_or_default();
        let mut ir_names = HashMap::default();
        for (ast_var, ir_var) in ir_vars {
          if let Some(name) = names.get(&ast_var) {
            ir_names.insert(ir_var, name.clone());
          }
        }
        let ir = this
          .ir_of(uri.clone())
          .map(|lower| ir_to_json(&mut printer, &ir_names, lower.ir));
        let simple_ir = this
          .simple_ir_of(uri.clone())
          .map(|ir| ir_to_json(&mut printer, &ir_names, ir));
        let wasm: Option<String> = this.wasm_of(uri.clone()).map(|wasm| {
          let mut out = PrintHtmlWrite::default();
          wasmprinter::Config::new()
            .fold_instructions(true)
            .indent_text("  ")
            .print(&wasm, &mut out)
            .expect("Failed to print wat from wasm");
          out.into()
        });

        json!({
          "cst": cst_json,
          "ast": ast_json,
          "ir": ir,
          "simple_ir": simple_ir,
          "wasm": wasm,
        })
      },
    )
  }

  pub fn ir_of(&self, uri: Uri) -> Option<LowerOut> {
    self.query(QueryKey::IrOf(uri), &self.db.ir_query, |this, key| {
      let QueryKey::IrOf(uri) = key else {
        unreachable!()
      };
      let types = this.types_of(uri.clone());
      // If we have errors, lowering will crash
      if !types.errors.is_empty() {
        return None;
      }

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
        // Just flagrantly cheating because we don't have real support for top level items.
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

mod prettyprint {
  use std::collections::HashMap;

  use pretty::{DocAllocator, DocBuilder, RcAllocator};
  use types_base::{Type, TypeVar};

  pub fn prettyprint_ty(ty: &Type) -> String {
    let mut pp = PrettyprintType::new();
    let doc = pp.pretty(ty, &RcAllocator);
    let mut out = String::new();
    doc.render_fmt(80, &mut out).unwrap();
    out
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

#[derive(Default)]
struct PrintHtmlWrite(String);
impl From<PrintHtmlWrite> for String {
  fn from(val: PrintHtmlWrite) -> Self {
    val.0
  }
}
impl wasmprinter::Print for PrintHtmlWrite {
  fn write_str(&mut self, s: &str) -> std::io::Result<()> {
    self.0.push_str(s);
    Ok(())
  }

  fn start_literal(&mut self) -> std::io::Result<()> {
    self.0.push_str("<span class=\"number\">");
    Ok(())
  }

  fn start_name(&mut self) -> std::io::Result<()> {
    self.0.push_str("<span class=\"variable\">");
    Ok(())
  }

  fn start_keyword(&mut self) -> std::io::Result<()> {
    self.0.push_str("<span class=\"keyword\">");
    Ok(())
  }

  fn start_type(&mut self) -> std::io::Result<()> {
    self.0.push_str("<span class=\"type\">");
    Ok(())
  }

  fn start_comment(&mut self) -> std::io::Result<()> {
    self.0.push_str("<span class=\"comment\">");
    Ok(())
  }

  fn reset_color(&mut self) -> std::io::Result<()> {
    self.0.push_str("</span>");
    Ok(())
  }

  fn supports_async_color(&self) -> bool {
    false
  }

  fn newline(&mut self) -> std::io::Result<()> {
    self.write_str("\n")
  }

  fn start_line(&mut self, binary_offset: Option<usize>) {
    let _ = binary_offset;
  }

  fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> std::io::Result<()> {
    struct Adapter<'a, T: ?Sized + 'a> {
      inner: &'a mut T,
      error: std::io::Result<()>,
    }

    impl<T: wasmprinter::Print + ?Sized> std::fmt::Write for Adapter<'_, T> {
      fn write_str(&mut self, s: &str) -> std::fmt::Result {
        match self.inner.write_str(s) {
          Ok(()) => Ok(()),
          Err(e) => {
            self.error = Err(e);
            Err(std::fmt::Error)
          }
        }
      }
    }

    let mut output = Adapter {
      inner: self,
      error: Ok(()),
    };
    match std::fmt::write(&mut output, args) {
      Ok(()) => Ok(()),
      Err(..) => output.error,
    }
  }

  fn print_custom_section(
    &mut self,
    name: &str,
    binary_offset: usize,
    data: &[u8],
  ) -> std::io::Result<bool> {
    let _ = (name, binary_offset, data);
    Ok(false)
  }
}
