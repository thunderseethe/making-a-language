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
}

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

mod wasm_printer {
  use logos::Logos;

  #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Logos)]
  #[repr(u16)]
  enum SyntaxKind {
    #[token("(")]
    LeftParen = 0, // '('
    #[token(")")]
    RightParen,    // ')'
    #[regex("\\p{alpha}\\w*")]
    Word,          // '+', '15'
    #[regex("\\s+")]
    Whitespace,    // whitespaces is explicit
    #[regex("\\d+")]
    Number,
    Error,         // as well as errors

    // composite nodes
    List, // `(+ 2 3)`
    Atom, // `+`, `15`, wraps a WORD token
    Root, // top-level node: a list of s-expressions
  }
  use SyntaxKind::*;

  impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
      Self(kind as u16)
    }
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
  enum Lang {}
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

  /// GreenNode is an immutable tree, which is cheap to change,
  /// but doesn't contain offsets and parent pointers.
  use rowan::GreenNode;

  /// You can construct GreenNodes by hand, but a builder
  /// is helpful for top-down parsers: it maintains a stack
  /// of currently in-progress nodes
  use rowan::GreenNodeBuilder;

  /// The parse results are stored as a "green tree".
  /// We'll discuss working with the results later
  struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
  }

  /// Now, let's write a parser.
  /// Note that `parse` does not return a `Result`:
  /// by design, syntax tree can be built even for
  /// completely invalid source code.
  fn parse(text: &str) -> Parse {
    struct Parser<'a> {
      tokens: std::iter::Peekable<logos::Lexer<'a, SyntaxKind>>,
      content: &'a str,
      /// the in-progress tree.
      builder: GreenNodeBuilder<'static>,
      /// the list of syntax errors we've accumulated
      /// so far.
      errors: Vec<String>,
    }

    /// The outcome of parsing a single S-expression
    enum SexpRes {
      /// An S-expression (i.e. an atom, or a list) was successfully parsed
      Ok,
      /// Nothing was parsed, as no significant tokens remained
      Eof,
      /// An unexpected ')' was found
      RParen,
    }

    impl Parser {
      fn parse(mut self) -> Parse {
        // Make sure that the root node covers all source
        self.builder.start_node(Root.into());
        // Parse zero or more S-expressions
        loop {
          match self.sexp() {
            SexpRes::Eof => break,
            SexpRes::RParen => {
              self.builder.start_node(Error.into());
              self.errors.push("unmatched `)`".to_string());
              self.bump(); // be sure to chug along in case of error
              self.builder.finish_node();
            }
            SexpRes::Ok => (),
          }
        }
        // Don't forget to eat *trailing* whitespace
        self.skip_ws();
        // Close the root node.
        self.builder.finish_node();

        // Turn the builder into a GreenNode
        Parse {
          green_node: self.builder.finish(),
          errors: self.errors,
        }
      }
      fn list(&mut self) {
        assert_eq!(self.current(), Some(LeftParen));
        // Start the list node
        self.builder.start_node(List.into());
        self.bump(); // '('
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
        // close the list node
        self.builder.finish_node();
      }

      fn sexp(&mut self) -> SexpRes {
        // Eat leading whitespace
        self.skip_ws();
        // Either a list, an atom, a closing paren,
        // or an eof.
        let t = match self.current() {
          None => return SexpRes::Eof,
          Some(RightParen) => return SexpRes::RParen,
          Some(t) => t,
        };
        match t {
          LeftParen => self.list(),
          Word => {
            self.builder.start_node(Atom.into());
            self.bump();
            self.builder.finish_node();
          }
          Error => self.bump(),
          _ => unreachable!(),
        }
        SexpRes::Ok
      }
      /// Advance one token, adding it to the current branch of the tree builder.
      fn bump(&mut self) {
        let (kind, text) = self.tokens.pop().unwrap();
        self.builder.token(kind.into(), text.as_str());
      }
      /// Peek at the first unprocessed token
      fn current(&self) -> Option<SyntaxKind> {
        self.tokens.last().map(|(kind, _)| *kind)
      }
      fn skip_ws(&mut self) {
        while self.current() == Some(Whitespace) {
          self.bump()
        }
      }
    }

    let tokens = SyntaxKind::lexer(text);
    Parser {
      tokens: tokens,
      content: text,
      builder: GreenNodeBuilder::new(),
      errors: Vec::new(),
    }
    .parse()
  }

  /// To work with the parse results we need a view into the
  /// green tree - the Syntax tree.
  /// It is also immutable, like a GreenNode,
  /// but it contains parent pointers, offsets, and
  /// has identity semantics.

  type SyntaxNode = rowan::SyntaxNode<Lang>;

  #[allow(unused)]
  type SyntaxToken = rowan::SyntaxToken<Lang>;

  #[allow(unused)]
  type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

  impl Parse {
    fn syntax(&self) -> SyntaxNode {
      SyntaxNode::new_root(self.green_node.clone())
    }
  }
}
