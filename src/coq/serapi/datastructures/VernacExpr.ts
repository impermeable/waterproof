import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacExpr object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacExpr
 */
class VernacExpr extends CoqType {
  content: any;

  /**
   * Construct for the VernacExpr type
   * @param {Array} array Array to parse
   */
  constructor( array ) {
    super(array);
    const data = array;
    data[2] = convertToASTComp(array[2]);
    this.content = data[2];
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0) {
    const output = '';
    output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacExpr(this);
  }
}

/* istanbul ignore next */
export default VernacExpr;
