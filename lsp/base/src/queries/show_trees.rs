use rowan::Language;

use super::*;

impl QueryContext {
  pub fn show_trees_of(&self, uri: Uri) -> LSPAny {
    self.query(
      QueryKey::ShowTreesOf(uri.clone()),
      &self.db.show_trees_query,
      |this, _| {
        let (green, _) = this.cst_of(uri.clone());
        let desugar = this.desugar_of(uri.clone());
        let types = this.types_of(uri.clone());

        let root = SyntaxNode::<Lang>::new_root(green);

        let ast = zip_ast(desugar.ast, types.ast);
        let mut printer = PrettyprintType::new();
        let ast_json = ast_to_json(&mut printer, ast);

        let cst_json = cst_to_json(NodeOrToken::Node(root));

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
        let wasm: Option<LSPAny> = this.wasm_of(uri.clone()).map(|wasm| {
          let mut out = wasmprinter::PrintFmtWrite(String::new());
          wasmprinter::Config::new()
            .fold_instructions(true)
            .print(&wasm, &mut out)
            .expect("Failed to print wat from wasm");
          let mut html = PrintHtmlWrite::default();
          wasmprinter::Config::new()
              .fold_instructions(true)
              .indent_text("    ")
              .print(&wasm, &mut html)
              .expect("Failed to print wat from wasm");
          let parse = wasm_parser::parse(&out.0).syntax();
          json!({
            "cst": wasm_cst_to_json(parse),
            "source": html.0
          })
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
}

fn cst_to_json<L: Language>(nort: NodeOrToken<SyntaxNode<L>, SyntaxToken<L>>) -> LSPAny {
  let kind: u64 = L::kind_to_raw(nort.kind()).0 as u64;
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

fn wasm_cst_to_json(
  nort: NodeOrToken<SyntaxNode<wasm_parser::Lang>, SyntaxToken<wasm_parser::Lang>>,
) -> LSPAny {
  fn is_trivia(
    nort: &NodeOrToken<SyntaxNode<wasm_parser::Lang>, SyntaxToken<wasm_parser::Lang>>,
  ) -> bool {
    nort.kind() == wasm_parser::SyntaxKind::Whitespace
      || nort.kind() == wasm_parser::SyntaxKind::LeftParen
      || nort.kind() == wasm_parser::SyntaxKind::RightParen
  }
  let kind: String = format!("{:?}", nort.kind());
  json!({
    "key": kind,
    "text": nort.as_token().map(|tok| tok.text()),
    "children": nort.as_node().map(|node| node.children_with_tokens().filter(|nort| !is_trivia(nort)).map(wasm_cst_to_json).collect::<Vec<_>>()),
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

mod wasm_parser {
  use logos::Logos;

  #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Logos)]
  #[repr(u16)]
  pub enum SyntaxKind {
    #[token("(")]
    LeftParen = 0,
    #[token(")")]
    RightParen,
    #[regex("[_\\p{alpha}][\\._\\w]*")]
    Word,
    #[regex("\\$[_\\w]+")]
    Var,
    #[regex("\\s+")]
    Whitespace,
    #[regex("\\d+")]
    Number,
    Error,

    // composite nodes
    List,
    #[regex("\\(;[^;\\)]*;\\)")]
    Comment,
    #[regex("\"[^\"]*\"")]
    StringLit,
    Root,
  }
  use SyntaxKind::*;

  impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
      Self(kind as u16)
    }
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum Lang {}
  impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
      assert!(raw.0 <= Root as u16);
      unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
      kind.into()
    }
  }

  use rowan::GreenNode;

  use rowan::GreenNodeBuilder;

  pub struct Parse {
    pub green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
  }

  pub fn parse(text: &str) -> Parse {
    struct Parser<'a> {
      tokens: std::iter::Peekable<logos::SpannedIter<'a, SyntaxKind>>,
      content: &'a str,
      builder: GreenNodeBuilder<'static>,
      errors: Vec<String>,
    }

    enum SexpRes {
      Ok,
      Eof,
      RParen,
    }

    impl<'a> Parser<'a> {
      fn parse(mut self) -> Parse {
        match self.sexp() {
          SexpRes::Eof => (),
          SexpRes::RParen => {
            self.builder.start_node(Error.into());
            self.errors.push("unmatched `)`".to_string());
            self.bump(); // be sure to chug along in case of error
            self.builder.finish_node();
          }
          SexpRes::Ok => (),
        }

        Parse {
          green_node: self.builder.finish(),
          errors: self.errors,
        }
      }

      fn list(&mut self) {
        self.builder.start_node(List.into());
        self.bump();
        loop {
          match self.sexp() {
            SexpRes::Eof => {
              self.errors.push("expected `)`".to_string());
              break;
            }
            SexpRes::RParen => {
              self.bump();
              break;
            }
            SexpRes::Ok => (),
          }
        }
        self.builder.finish_node();
      }

      fn sexp(&mut self) -> SexpRes {
        self.skip_ws();
        let t = match self.current() {
          None => return SexpRes::Eof,
          Some(RightParen) => return SexpRes::RParen,
          Some(t) => t,
        };
        match t {
          LeftParen => self.list(),
          Word | Var | Number | StringLit | Comment | Error => {
            self.bump();
          }
          t => unreachable!("{t:?}"),
        }
        SexpRes::Ok
      }

      fn bump(&mut self) {
        let (kind, text) = self.tokens.next().unwrap();
        self
          .builder
          .token(kind.unwrap_or(Error).into(), &self.content[text]);
      }

      fn current(&mut self) -> Option<SyntaxKind> {
        self
          .tokens
          .peek()
          .map(|(kind, _)| kind.unwrap_or(Error).into())
      }

      fn skip_ws(&mut self) {
        while self.current() == Some(Whitespace) {
          self.bump()
        }
      }
    }

    let tokens = SyntaxKind::lexer(text).spanned().peekable();
    Parser {
      tokens: tokens,
      content: text,
      builder: GreenNodeBuilder::new(),
      errors: Vec::new(),
    }
    .parse()
  }

  type SyntaxNode = rowan::SyntaxNode<Lang>;

  #[allow(unused)]
  type SyntaxToken = rowan::SyntaxToken<Lang>;

  #[allow(unused)]
  type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

  impl Parse {
    pub fn syntax(self) -> SyntaxElement {
      let root = SyntaxNode::new_root(self.green_node);
      rowan::NodeOrToken::Node(root)
    }
  }
}
