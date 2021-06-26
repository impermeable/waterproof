/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq CLocalAssum object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CLocalAssum
 */
class CLocalAssum extends CoqType {
  names: any;
  binderKind: any;
  expr: { locinfo: LocInfo; content: any; };

  /**
   * Constructor for CLocalAssum type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    console.warn('CLocalAssum', array);
    this.names = array[1].map((name) => ({
      locinfo: new LocInfo(['loc', name.loc]),
      content: convertToASTComp(name.v),
    }));
    this.binderKind = array[2];
    this.expr = {
      locinfo: new LocInfo(['loc', array[3].loc]),
      content: convertToASTComp(array[3].v),
    };
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    for (let i = 0; i < this.names.length; i++) {
      output = output.concat('Loc: ', this.names[i].locinfo.pprint(indent + 1),
          tab);
      output = output.concat(this.cprint(this.names[i].content, indent));
    }
    output = output.concat('Kind: ', this.binderKind, tab);
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent + 1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor): void {
    v.visitCLocalAssum(this);
  }
}

export default CLocalAssum;
