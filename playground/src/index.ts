import { autocompletion, closeBrackets, closeBracketsKeymap, completionKeymap } from '@codemirror/autocomplete'
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands'
import { bracketMatching, defaultHighlightStyle, foldGutter, foldKeymap, indentOnInput, syntaxHighlighting } from '@codemirror/language'
import { Diagnostic, linter, lintKeymap } from '@codemirror/lint'
import { highlightSelectionMatches, searchKeymap } from '@codemirror/search'
import { EditorState, Text } from '@codemirror/state'
import { crosshairCursor, drawSelection, dropCursor, EditorView, highlightActiveLine, highlightActiveLineGutter, highlightSpecialChars, keymap, lineNumbers, rectangularSelection } from '@codemirror/view'
import { oneDark } from '@codemirror/theme-one-dark'

import { languageServerSupport, LSPClient, LSPPlugin, Transport } from '@codemirror/lsp-client'
import type * as lsp from "vscode-languageserver-protocol"

import { node_set_spec, pellucidLanguage } from './parser';
import { jsonViewer } from './json_view';

import 'normalize.css'
import './style.css'

const localStorageKey = "initialText";
const initialText = getInitialText();
const targetElement = document.querySelector('#editor')!

const lsp_worker = new Worker(new URL("./worker", import.meta.url));

let max_log_length = 100;
let log_list = document.querySelector("#log-tab-content")!;
function createLogEntry(json: { id: string, method: string, params: any }): void {
  let msgEle = document.createElement("details");
  msgEle.classList.add("request");
  msgEle.dataset.id = json.id;
  let id = json.id ? `[${json.id}] ` : '';

  msgEle.innerHTML = `
      <summary><h4>${id}${json.method}</h4></summary>
      <ul>
        <li> 
          <details class="params">
            <summary><h5>Params</h5></summary>
            ${jsonViewer(json.params, true)}
          </details>
        </li>
      </ul>`;
  log_list.prepend(msgEle);
  if (log_list.childElementCount > max_log_length) {
    log_list.lastChild?.remove();
  }
}

function addLogEntryResponse(data: { id: string, result: any }): void {
  let msgEle = document.querySelector(`details.request[data-id='${data.id}'] ul`);
  if (!msgEle) { return; }
  if (msgEle) {
    let response = document.createElement("li");
    response.innerHTML = `
      <details class="response">
        <summary><h5>Response</h5></summary>
        ${jsonViewer(data.result, true)}
      </details>
    `;
    msgEle.appendChild(response);
  }
}

class WorkerTransport implements Transport {
  worker: Worker;
  handlers: ((value: string) => void)[] = [];

  constructor(worker: Worker) {
    this.worker = worker;
    this.worker.onerror = (e) => console.error('worker error', e);
    this.worker.onmessageerror = (e) => console.error('message error', e);
    this.worker.onmessage = (e) => {
      console.log('main received', e.data);
      let str = JSON.stringify(e.data);
      for (let handler of this.handlers) {
        handler(str);
      }
      addLogEntryResponse(e.data);
    }
  }

  send(message: string): void {
    if (this.worker) {
      let json = JSON.parse(message);
      console.log('main sent', json);
      this.worker.postMessage(json);
      createLogEntry(json);
    }
  }

  subscribe(handler: (value: string) => void): void {
    this.handlers.push(handler)
  }

  unsubscribe(handler: (value: string) => void): void {
    this.handlers = this.handlers.filter(h => h != handler);
  }
}

var treeViews = {
  cst: document.querySelector("#cst-tab-content")!,
  ast: document.querySelector("#ast-tab-content")!,
  ir: document.querySelector("#ir-tab-content")!,
  simple_ir: document.querySelector("#simple-ir-tab-content")!,
  wasm: document.querySelector("#wasm-tab-content")!,
};

let debounceTimer: NodeJS.Timeout;

// Postpone launching until worker has loaded
lsp_worker.onmessage = (e) => {
  if (e.data != 'ready') {
    console.error(e.data);
  }
  let transport = new WorkerTransport(lsp_worker);
  let client = new LSPClient({ rootUri: 'playground' }).connect(transport);
  let view = new EditorView({
    parent: targetElement,
    state: EditorState.create({
      doc: initialText,
      extensions: [
        lineNumbers(),
        highlightActiveLineGutter(),
        highlightSpecialChars(),
        history(),
        foldGutter(),
        drawSelection(),
        dropCursor(),
        EditorState.allowMultipleSelections.of(true),
        indentOnInput(),
        syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
        bracketMatching(),
        closeBrackets(),
        autocompletion(),
        rectangularSelection(),
        crosshairCursor(),
        highlightActiveLine(),
        highlightSelectionMatches(),
        keymap.of([
          ...closeBracketsKeymap,
          ...defaultKeymap,
          ...searchKeymap,
          ...historyKeymap,
          ...foldKeymap,
          ...completionKeymap,
          ...lintKeymap,
        ]),
        pellucidLanguage,
        oneDark,
        languageServerSupport(client, "playground"),
        linter(lspLintSource, {
          hideOn: tr => tr.docChanged
        }),
        EditorView.updateListener.of((update) => {
          if (!update.docChanged) return;
          let plugin = LSPPlugin.get(update.view);
          if (!plugin) return;
          plugin.client.sync();
          clearTimeout(debounceTimer);
          debounceTimer = setTimeout(() => {
            showTrees(plugin);
            updateReplWasm(plugin);
          }, 300);
        }),
        EditorView.theme({
          "&": {
            width: "100%",
            height: "100%",
          },
          ".cm-content": {
            fontFamily: 'FiraCode',
          },
          ".cm-tooltip": {
            zIndex: "150",
          },
        })
      ],
    }),
  });
  let plugin = LSPPlugin.get(view);
  if (plugin) {
    plugin.client.sync();
    showTrees(plugin);
    updateReplWasm(plugin);
  }

  window.addEventListener('beforeunload', (_) => {
    if (!storageAvailable()) return;
    window.localStorage.setItem(localStorageKey, view.state.doc.toString());
  });
}

function updateReplWasm(plugin: LSPPlugin): void {
  plugin.client.request<lsp.ExecuteCommandParams, lsp.LSPAny>("workspace/executeCommand", {
    command: 'compile_wasm',
    arguments: ['playground'],
  }).then((any) => {
    let wasm: { kind: 'ok', wasm_bytes?: Array<number> } = any;
    if (!wasm.wasm_bytes) { return null; }
    let buffer = new Uint8Array(wasm.wasm_bytes);
    return WebAssembly.instantiate(buffer);
  }).then((module) => {
    if (!module) return;
    let main = module.instance.exports["main"]
    // We expect main to always be a function.
    // This is mainly just for typechecking.
    if (typeof main !== 'function') {
      console.error('expected a function', main);
      return;
    }
    // Only call our function if it takes no parameters.
    // Otherwise our function is the value and we should print it as is.
    let value =
      main.length == 0
       ? main()
       : main;
    let output = 
      // If our value is a wasm struct (which has typeof object), it does not support string conversion.
      // We handle that by manually converting it to a string here.
      typeof value == 'object'
        ? 'struct'
        : `${value}`;
    let ele = document.querySelector("#output-tab-content")! as HTMLElement;
    ele.innerHTML = `<span class="output">⟫ ${output}</span>`;
  });
}

function showTrees(plugin: LSPPlugin): void {
  plugin.client.request<lsp.ExecuteCommandParams, lsp.LSPAny>("workspace/executeCommand", {
    command: 'show_trees',
    arguments: ['playground'],
  }).then((any) => {
    let trees: Trees = any;
    {
      let ul = document.createElement("ul");
      ul.appendChild(cstView(trees.cst, plugin.view.state));
      treeViews.cst.replaceChildren(ul);
    }
    {
      let ul = document.createElement("ul");
      ul.appendChild(astIrView(trees.ast));
      treeViews.ast.replaceChildren(ul);
    }
    if (trees.ir) {
      let ul = document.createElement("ul");
      ul.appendChild(astIrView(trees.ir));
      treeViews.ir.replaceChildren(ul);
    } else {
      treeViews.ir.replaceChildren();
    }
    if (trees.simple_ir) {
      let ul = document.createElement("ul");
      ul.appendChild(astIrView(trees.simple_ir));
      treeViews.simple_ir.replaceChildren(ul);
    } else {
      treeViews.simple_ir.replaceChildren();
    }
    if (trees.wasm) {
      let ul = document.createElement("ul");
      ul.appendChild(wasmCstView(trees.wasm.cst));
      treeViews.wasm.replaceChildren(ul);
      let button = document.createElement("button");
      button.setAttribute('style', 'position: absolute; right: 10px; top: -2px;')
      button.innerHTML = `View Source`;
      button.setAttribute('popovertarget', 'wasm-source');
      let dialog = document.createElement("dialog");
      dialog.setAttribute('style', 'overflow: scroll; height: 80%; width: 80%;');
      dialog.setAttribute('popover', '');
      dialog.setAttribute('id', 'wasm-source');
      dialog.innerHTML = `
        <code><pre>${trees.wasm.source}</pre></code>
      `
      treeViews.wasm.appendChild(button);
      treeViews.wasm.appendChild(dialog);
    } else {
      treeViews.wasm.replaceChildren();
    }
  })
}

type Trees = {
  cst: Cst,
  ast: AstIr,
  ir: AstIr | null,
  simple_ir: AstIr | null,
  wasm: { cst: WasmCst, source: string } | null
}


type Cst = {
  key: number,
  text_range: { start: number, end: number },
  children?: [Cst]
}
function cstView(cst: Cst, state: EditorState): HTMLElement {
  let styles: { [s: string]: string } = {
    'LetKw': 'keyword',
    'Int': 'number',
    'Identifier': 'variable',
    'LeftParen': 'punctuation',
    'RightParen': 'punctuation',
    'Backslash': 'punctuation',
    'Arrow': 'punctuation'
  };
  let node = node_set_spec.node_types[cst.key];
  let li = document.createElement("li");
  if (cst.children) {
    let summary = document.createElement("summary");
    summary.innerText = `${node.name} ${cst.text_range.start}..${cst.text_range.end}`;
    let ul = document.createElement("ul");
    for (let child of cst.children) {
      ul.appendChild(cstView(child, state));
    }
    let details = document.createElement("details");
    details.appendChild(summary);
    details.appendChild(ul);
    li.appendChild(details);
  } else {
    let slice =
      state
        .sliceDoc(cst.text_range.start, cst.text_range.end);
    if (node.name == "Whitespaces") {
      li.innerText =
        slice
          .replaceAll(/\s/g, '␣')
          .replaceAll(/\n/g, '\\n')
          .replaceAll(/\t/g, '\\t');
    } else {
      if (node.name in styles) {
        li.innerHTML =
          `<span class="${styles[node.name]}">${slice}</span>`;
      } else {
        li.innerText = slice;
      }
    }
  }
  return li;
}

type AstIr
  = { kind: "var", name: string, type: string }
  | { kind: "int", value: number }
  | { kind: "hole", type: string }
  | { kind: "app", fun: AstIr, arg: AstIr }
  | { kind: "fun", name: string, type: string, body: AstIr }
  | { kind: "ty_fun", ty_fun_kind: string, body: AstIr }
  | { kind: "ty_app", ty_fun: AstIr, type: string }
  | { kind: "local", name: string, type: string, defn: AstIr, body: AstIr };


function astIrView(tree: AstIr): HTMLElement {
  function variable(
    tree: { name: string, type: string }
  ): string {
    return `<div class="leaf">
        <a class="variable" data-title=": ${tree.type}">${tree.name}</a>
      </div>`;
  }
  switch (tree.kind) {
    case 'var': {
      let li = document.createElement("li")!;
      li.innerHTML = variable(tree);
      return li;
    }
    case 'int': {
      let li = document.createElement("li");
      li.innerHTML = `
        <div class="leaf">
          Int <span class="number">${tree.value}</span>
        </div>`;
      return li;
    }
    case 'hole': {
      let li = document.createElement("li");
      li.innerText = `<div class="leaf">
        <span class="hole">_</span>
        <span class="type">${tree.type}</span>
      </div>`;
      return li;
    }
    case 'app': {
      return nested('App', [
        astIrView(tree.fun),
        astIrView(tree.arg)
      ]);
    }
    case 'fun': {
      let li = document.createElement("li")!;
      li.innerHTML = variable(tree);
      return nested('Fun', [
        li,
        astIrView(tree.body)
      ]);
    }
    case 'ty_fun': {
      let li = document.createElement("li");
      li.innerText = `${tree.ty_fun_kind}`;
      return nested('TyFun', [
        li,
        astIrView(tree.body)
      ]);
    }
    case 'ty_app': {
      let li = document.createElement("li");
      li.innerText = `${tree.type}`;
      return nested('TyApp', [
        astIrView(tree.ty_fun),
        li
      ]);
    }
    case 'local': {
      let li = document.createElement("li");
      li.innerHTML = variable(tree);
      return nested('Local', [
        li,
        astIrView(tree.defn),
        astIrView(tree.body)
      ]);
    }
  }
}
type WasmCst = {
  key: string,
  text?: string,
  children?: WasmCst[],
}
function wasmCstView(cst: WasmCst): HTMLElement {
  switch (cst.key) {
    case 'List': {
      var children: WasmCst[] = cst.children ?? [];
      if (children[0].key == 'Word') {
        let tail = children.slice(1);
        return nested(children[0].text ?? "missing text" , tail.map(wasmCstView));
      }
      return nested('List', children.map(wasmCstView));
    }
    case 'Word': {
      let li = document.createElement("li")!;
      li.innerHTML = `
        <div class="leaf">
          ${cst.text}
        </div>`;
      return li;
    }
    case 'Var': {
      let li = document.createElement("li")!;
      li.innerHTML = `
        <div class="leaf">
          <span class="variable">${cst.text}</span>
        </div>`;
      return li;
    }
    case 'Number': {
      let li = document.createElement("li");
      li.innerHTML = `
        <div class="leaf">
          <span class="number">${cst.text}</span>
        </div>`;
      return li;
    }
    case 'StringLit': {
      let li = document.createElement("li");
      li.innerHTML = `
        <div class="leaf">
          <span class="string">${cst.text}</span>
        </div>`;
      return li;
    }
    case 'Comment': {
      let li = document.createElement("li");
      li.innerHTML = `
        <div class="leaf">
          <span class="comment">${cst.text}</span>
        </div>`;
      return li;
    }
    default: {
      let li = document.createElement("li");
      li.innerHTML = `
        <div class="leaf">
          <span class="error">"${cst.text}"</span>
        </div>`;
      return li;
    }
  }
}

function nested(summary: string, elements: HTMLElement[]): HTMLElement {
  let summaryHtml = document.createElement("summary");
  summaryHtml.innerText = summary;

  let ul = document.createElement("ul");
  for (let element of elements) {
    ul.appendChild(element);
  }

  let details = document.createElement("details");
  details.appendChild(summaryHtml);
  details.appendChild(ul);

  let li = document.createElement("li");
  li.appendChild(details);
  return li;
}

function fromPosition(doc: Text, pos: lsp.Position): number {
  let line = doc.line(pos.line + 1)
  return line.from + pos.character
}

function lspLintSource(view: EditorView): Promise<Diagnostic[]> {
  let plugin = LSPPlugin.get(view);
  if (!plugin) { return Promise.resolve([]); }
  plugin.client.sync();
  return plugin.client.request<lsp.DocumentDiagnosticParams, lsp.DocumentDiagnosticReport>("textDocument/diagnostic", {
    textDocument: { uri: plugin.uri },
  }).then((report) => {
    switch (report.kind) {
      case 'unchanged': return [];
      case 'full':
        let diags: Diagnostic[] = report.items.map((diag: lsp.Diagnostic): Diagnostic => {
          return {
            from: fromPosition(view.state.doc, diag.range.start),
            to: fromPosition(view.state.doc, diag.range.end),
            severity: (() => {
              switch (diag.severity) {
                case 1:
                  return 'error';
                case 2:
                  return 'warning';
                case 3:
                  return 'info';
                case 4:
                  return 'hint';
                default:
                  return 'error';
              }
            })(),
            source: diag.source,
            message: diag.message,
          };
        });
        return diags;
    }
  });
}


function getInitialText(): string {
  if (storageAvailable()) {
    let text = window.localStorage.getItem(localStorageKey);
    if (text) {
      return text;
    }
  }
  return `let one = |s||z| s z;
let add = |m||n||s||z| m s (n s z);
let two = add one one;
add two two`;
}

function storageAvailable(): boolean | undefined {
  let storage;
  try {
    storage = window.localStorage;
    const x = "__storage_test__";
    storage.setItem(x, x);
    storage.removeItem(x);
    return true;
  } catch (e) {
    return (
      e instanceof DOMException &&
      e.name === "QuotaExceededError" &&
      // acknowledge QuotaExceededError only if there's something already stored
      storage &&
      storage.length !== 0
    );
  }
}
