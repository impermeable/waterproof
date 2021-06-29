import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacProof object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacProof
 */
class VernacProof extends CoqType implements Visitable {
  sectionSubsetExpr: any;
  rawGenericArg: any;

  /**
   * Constructor for the VernacProof type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.rawGenericArg = array[0] || {};
    this.sectionSubsetExpr = array[1] || {};
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0) {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Arg: ', this.rawGenericArg.toString(), tab);
    output = output.concat('Expr: ', this.sectionSubsetExpr.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacProof(this);
  }
}

/* istanbul ignore next */
export default VernacProof;
