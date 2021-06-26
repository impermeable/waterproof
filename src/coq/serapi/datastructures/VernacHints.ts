import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacHints object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacHints
 */
class VernacHints extends CoqType implements Visitable {
  strings: any;
  hintExpr: any;

  /**
   * Constructor for the VernacHints type
   * @param {Array} array Array to parse
   */
  constructor( array ) {
    super(array);
    console.log('VernacHints', array);
    this.strings = array[1];
    this.hintExpr = convertToASTComp(array[2]);
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
    output = output.concat('Strings: ', this.strings, tab);
    if (!Array.isArray(this.hintExpr)) {
      output = output.concat('Hint: ', this.hintExpr.pprint(indent+1), tab);
    } else {
      output = output.concat('Hint: ', tab, '\t', this.hintExpr.toString(),
          tab);
    }
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacHints(this);
  }
}

export default VernacHints;
