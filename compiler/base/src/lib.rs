use std::fmt::Debug;
use std::sync::Arc;

use closure_convert_base::{closure_convert, ItemId};
use dashmap::DashMap;
use desugar_base::{desugar, DesugarError, ErrorKind};
use emit_base::emit_wasm;
use lowering_base::{self as ir, lower};
use monomorph_base::trivial_monomorph;
use name_resolution_base::{name_resolution, NameResolutionError};
use parser_base::rowan::NodeOrToken;
use parser_base::{all_syntax, Flavor, Lang, ParseNode, Syntax, SyntaxNode};
use simplify_base::simplify;

use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::lsp_types::{
  CompletionOptions, CompletionParams, CompletionResponse, DidChangeTextDocumentParams,
  DidOpenTextDocumentParams, Hover, HoverContents, HoverParams, HoverProviderCapability,
  InitializeParams, InitializeResult, InitializedParams, MarkedString, ServerCapabilities,
  TextDocumentSyncCapability, TextDocumentSyncKind,
};
use tower_lsp_server::{Client, LanguageServer, LspService, Server};
use types_base::{type_infer, TypeError, TypeErrorKind};

use wasm_bindgen::prelude::*;
use wasm_streams::{ReadableStream, WritableStream};

mod queries;
use queries::Database;
use web_sys::js_sys;

pub enum CompilerError {
  Desugar(DesugarError),
  NameResolution(NameResolutionError),
  Type(TypeError),
}
impl From<DesugarError> for CompilerError {
  fn from(value: DesugarError) -> Self {
    Self::Desugar(value)
  }
}
impl From<NameResolutionError> for CompilerError {
  fn from(value: NameResolutionError) -> Self {
    Self::NameResolution(value)
  }
}
impl From<TypeError> for CompilerError {
  fn from(value: TypeError) -> Self {
    Self::Type(value)
  }
}

#[wasm_bindgen(getter_with_clone)]
#[derive(Clone)]
pub struct NodeSpec {
  pub id: usize,
  pub name: String,
  pub top: bool,
  pub error: bool,
  pub skipped: bool,
}

#[wasm_bindgen(getter_with_clone)]
pub struct TreeData {
  pub buffer: Vec<usize>,
  pub top_id: usize,
}

fn node_type(syn: Syntax) -> NodeSpec {
  NodeSpec {
    id: (syn as u16) as usize,
    name: format!("{:?}", syn),
    top: syn == Syntax::Program,
    error: syn == Syntax::Error,
    skipped: false,
  }
}

fn post_order(cst: parser_base::rowan::SyntaxElement<Lang>, out: &mut Vec<usize>) -> usize {
  let mut count = 0;
  let kind = cst.kind();
  let range: std::ops::Range<usize> = cst.text_range().into();

  if let NodeOrToken::Node(node) = cst {
    for child in node.children_with_tokens() {
      count += post_order(child, out);
    }
  }
  count += 4;
  let node_id = kind as u16;
  out.push(node_id.into());
  out.push(range.start);
  out.push(range.end);
  out.push(count);
  count
}

#[wasm_bindgen(getter_with_clone)]
pub struct NodeSet {
  pub node_types: Vec<NodeSpec>,
  pub top_id: usize,
}

#[wasm_bindgen]
pub fn lezer_node_types() -> NodeSet {
  NodeSet {
    node_types: all_syntax().map(node_type).collect(),
    top_id: (Syntax::Program as u16) as usize,
  }
}

#[wasm_bindgen]
pub fn lezer_parse(input: &str) -> Vec<usize> {
  console_error_panic_hook::set_once();

  let (cst, _) = parser_base::parse(input);
  let mut buffer = vec![];
  let _ = post_order(NodeOrToken::Node(SyntaxNode::new_root(cst)), &mut buffer);
  buffer
}

#[wasm_bindgen]
pub struct ServerIo {
  recv: web_sys::ReadableStream,
  send: web_sys::WritableStream,
}

#[wasm_bindgen]
impl ServerIo {
  #[wasm_bindgen(constructor)]
  pub fn new(recv: web_sys::ReadableStream, send: web_sys::WritableStream) -> Self {
    Self { recv, send }
  }
}

#[wasm_bindgen]
pub async fn lsp(config: ServerIo) -> std::result::Result<(), JsValue> {
  console_error_panic_hook::set_once();

  let input = ReadableStream::from_raw(config.recv).into_async_read();
  let output = WritableStream::from_raw(config.send).into_async_write();

  let (lsp, socket) = LspService::new(PellucidLsp::new);

  Server::new(input, output, socket).serve(lsp).await;

  Ok(())
}

#[derive(Debug)]
struct PellucidLsp {
  client: Client,
  // We only support a single document right now, so we don't need more complicated handling than
  // this.
  database: Arc<Database>,
}

impl PellucidLsp {
  fn new(client: Client) -> Self {
    Self {
      client,
      database: Arc::new(Database::default()),
    }
  }
}

impl LanguageServer for PellucidLsp {
  async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
    Ok(InitializeResult {
      capabilities: ServerCapabilities {
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions::default()),
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        ..Default::default()
      },
      ..Default::default()
    })
  }

  async fn initialized(&self, _: InitializedParams) {
    // TODO: Should we do anything here?
  }

  async fn did_open(&self, params: DidOpenTextDocumentParams) {
    self
      .database
      .set_input(params.text_document.uri, params.text_document.text);
  }

  async fn hover(&self, _: HoverParams) -> Result<Option<tower_lsp_server::lsp_types::Hover>> {
    Ok(Some(Hover {
      range: None,
      contents: HoverContents::Scalar(MarkedString::from_language_code(
        "pellucid".to_string(),
        "test hover".to_string(),
      )),
    }))
  }

  async fn did_change(&self, params: DidChangeTextDocumentParams) {
    let uri = params.text_document.uri;
    let newlines = self.database.newlines_of(uri.clone());
    let mut content = self.database.content_of(uri.clone());
    for change in params.content_changes {
      if let Some(range) = change.range {
        if let Some(bytes) = newlines.byte_range_for(range) {
          content.insert_str(bytes.start, &change.text);
        } else {
          // If we can't construct a byte range, it's because our range is past the end of the
          // string.
          // Treat this as an append.
          content.push_str(&change.text);
        }
      } else {
        // If no range is present, change is the full document.
        // If we're replacing the entire text, there will only be one change, so we don't have to
        // worry about clobbering content here.
        content = change.text
      }
    }
    web_sys::console::log_1(&JsValue::from_str(&content));
    self.database.set_input(uri.clone(), content);
    let diags = self.database.diagnostics(uri.clone());
    self
      .client
      .publish_diagnostics(
        uri,
        diags,
        Some(params.text_document.version),
      )
      .await;
  }

  async fn completion(&self, _: CompletionParams) -> Result<Option<CompletionResponse>> {
    Ok(None)
  }

  async fn shutdown(&self) -> Result<()> {
    Ok(())
  }
}
