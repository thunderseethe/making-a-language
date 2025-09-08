use std::fmt::Debug;
use std::str::FromStr;
use std::sync::Arc;

use desugar_base::DesugarError;
use name_resolution_base::NameResolutionError;
use parser_base::{rowan::{NodeOrToken, SyntaxNode}, Lang, Syntax, all_syntax};

use serde_json::json;
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::lsp_types::{
  CompletionOptions, CompletionParams, CompletionResponse, DiagnosticOptions,
  DiagnosticServerCapabilities, DidChangeTextDocumentParams, DidOpenTextDocumentParams,
  DocumentDiagnosticReportResult, ExecuteCommandOptions, ExecuteCommandParams,
  FullDocumentDiagnosticReport, GotoDefinitionParams, GotoDefinitionResponse, HoverParams,
  HoverProviderCapability, InitializeParams, InitializeResult, LSPAny, OneOf,
  RelatedFullDocumentDiagnosticReport, RelatedUnchangedDocumentDiagnosticReport,
  ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
  UnchangedDocumentDiagnosticReport, Uri,
};
use tower_lsp_server::{Client, LanguageServer, LspService, Server};
use types_base::TypeError;

use wasm_bindgen::prelude::*;
use wasm_streams::{ReadableStream, WritableStream};

mod queries;
use queries::{Database, graph::DepGraph};

use self::queries::QueryContext;

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
    name: format!("{syn:?}"),
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
  dep_graph: Arc<DepGraph>,
}

impl PellucidLsp {
  fn new(client: Client) -> Self {
    Self {
      client,
      database: Arc::new(Database::default()),
      dep_graph: Arc::new(DepGraph::default()),
    }
  }

  fn root_query_context(&self) -> QueryContext {
    QueryContext::with_root(self.database.clone(), self.dep_graph.clone())
  }
}

impl LanguageServer for PellucidLsp {
  async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
    Ok(InitializeResult {
      capabilities: ServerCapabilities {
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions::default()),
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
          inter_file_dependencies: false,
          workspace_diagnostics: true,
          ..Default::default()
        })),
        definition_provider: Some(OneOf::Left(true)),
        references_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Left(true)),
        execute_command_provider: Some(ExecuteCommandOptions {
          commands: vec!["show_trees".to_string(), "compile_wasm".to_string()],
          ..Default::default()
        }),
        ..Default::default()
      },
      ..Default::default()
    })
  }

  async fn did_open(&self, params: DidOpenTextDocumentParams) {
    self
      .database
      .set_input(params.text_document.uri, params.text_document.text);
  }

  async fn did_change(&self, params: DidChangeTextDocumentParams) {
    let uri = params.text_document.uri;
    let ctx = self.root_query_context();
    let newlines = ctx.newlines_of(uri.clone());
    let mut content = ctx.content_of(uri.clone());
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
    self.database.set_input(uri.clone(), content);
    let diags = ctx.diagnostics(uri.clone());
    self
      .client
      .publish_diagnostics(uri, diags, Some(params.text_document.version))
      .await;
  }

  async fn diagnostic(
    &self,
    params: tower_lsp_server::lsp_types::DocumentDiagnosticParams,
  ) -> Result<DocumentDiagnosticReportResult> {
    let ctx = self.root_query_context();
    let diags = ctx.diagnostics(params.text_document.uri);
    if diags.is_empty() {
      return Ok(DocumentDiagnosticReportResult::Report(
        RelatedUnchangedDocumentDiagnosticReport {
          related_documents: None,
          unchanged_document_diagnostic_report: UnchangedDocumentDiagnosticReport {
            result_id: "unchanged".to_string(),
          },
        }
        .into(),
      ));
    }
    Ok(DocumentDiagnosticReportResult::Report(
      RelatedFullDocumentDiagnosticReport {
        related_documents: None,
        full_document_diagnostic_report: FullDocumentDiagnosticReport {
          result_id: None,
          items: diags,
        },
      }
      .into(),
    ))
  }

  async fn goto_definition(
    &self,
    params: GotoDefinitionParams,
  ) -> Result<Option<GotoDefinitionResponse>> {
    let ctx = self.root_query_context();
    let uri = params.text_document_position_params.text_document.uri;

    let Some(range) = ctx.definition_of(uri.clone(), params.text_document_position_params.position)
    else {
      return Ok(None);
    };
    Ok(Some(GotoDefinitionResponse::Scalar(
      tower_lsp_server::lsp_types::Location {
        // This could be different once we have different files, but for now uri is always the same.
        uri,
        range,
      },
    )))
  }

  async fn hover(&self, params: HoverParams) -> Result<Option<tower_lsp_server::lsp_types::Hover>> {
    let uri = params.text_document_position_params.text_document.uri;
    let position = params.text_document_position_params.position;
    let ctx = self.root_query_context();
    let Some(sync_node) = ctx.syntax_node_starting_at(uri.clone(), position) else {
      web_sys::console::log_1(&JsValue::from_str(&format!(
        "No node start at {position:?}"
      )));
      return Ok(None);
    };
    Ok(ctx.hover_of(uri.clone(), sync_node.clone()))
  }

  async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
    let ctx = self.root_query_context();
    let completions = ctx.completion_of(
      params.text_document_position.text_document.uri,
      params.text_document_position.position,
    );
    Ok(completions)
  }

  async fn execute_command(&self, params: ExecuteCommandParams) -> Result<Option<LSPAny>> {
    match params.command.as_str() {
      "show_trees" => {
        let LSPAny::String(string) = &params.arguments[0] else {
          return Err(tower_lsp_server::jsonrpc::Error {
            code: tower_lsp_server::jsonrpc::ErrorCode::InvalidParams,
            message: "Expected a string as first argument to \"show_trees\" command".into(),
            data: None,
          });
        };
        let uri = Uri::from_str(string.as_str()).expect("Invalid Uri passed to command");
        let ctx = self.root_query_context();
        let json = ctx.show_trees_of(uri);

        Ok(Some(json))
      }
      "compile_wasm" => {
        let LSPAny::String(string) = &params.arguments[0] else {
          return Err(tower_lsp_server::jsonrpc::Error {
            code: tower_lsp_server::jsonrpc::ErrorCode::InvalidParams,
            message: "Expected a string as first argument to \"compile_wasm\" command".into(),
            data: None,
          });
        };
        let uri = Uri::from_str(string.as_str()).expect("Invalid Uri passed to command");
        let ctx = self.root_query_context();
        let wasm_bytes = ctx.wasm_of(uri.clone());

        Ok(Some(json!({
          "wasm_bytes": wasm_bytes
        })))
      }
      _ => Ok(None),
    }
  }

  async fn shutdown(&self) -> Result<()> {
    Ok(())
  }
}
