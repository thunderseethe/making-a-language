import { defineLanguageFacet, Language } from '@codemirror/language';
import { Input, NodeSet, NodeType, Parser, PartialParse, Tree, TreeFragment } from '@lezer/common'
import { styleTags, tags } from '@lezer/highlight'
import { lezer_parse, lezer_node_types } from 'lsp-base'

export const node_set_spec = lezer_node_types();

class PellucidParser extends Parser {
  createParse(
    input: Input,
    _fragments: readonly TreeFragment[],
    _ranges: readonly { from: number; to: number }[]
  ): PartialParse {
    let node_types = node_set_spec.node_types.map((spec) => NodeType.define(spec));
    let node_set = new NodeSet(node_types).extend(
      styleTags({
        LetKw: tags.keyword,
        Int: tags.number,
        Var: tags.variableName,
        "LeftParen RightParen": tags.paren,
        "App/Var": tags.function(tags.variableName),
        Backslash: tags.punctuation,
        Arrow: tags.punctuation
      }));

    return new ExprContext(input, node_set, node_set_spec.top_id);
  }
}

class ExprContext implements PartialParse {
  input: Input;
  node_set: NodeSet;
  top_id: number;

  constructor(
    input: Input,
    node_set: NodeSet,
    top_id: number
  ) {
    this.input = input;
    this.node_set = node_set;
    this.top_id = top_id;
  }

  parsedPos: number = 0;
  stoppedAt: number = 0;


  advance(): Tree | null {
    let buffer = lezer_parse(this.input.read(0, this.input.length))
    let tree = Tree.build({
      buffer: Array.from(buffer),
      nodeSet: this.node_set,
      topID: this.top_id
    });
    this.parsedPos = tree.length;
    this.stoppedAt = tree.length;
    return tree;
  }

  stopAt(_: number) {
    throw new Error('Method not implemented.')
  }
}

export const pellucidLanguage = new Language(
  defineLanguageFacet({}),
  new PellucidParser(),
)
