import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/* eslint-disable require-jsdoc */
class VernacProof extends CoqType implements Visitable {
  sectionSubsetExpr: any;
  rawGenericArg: any;
  // TODO: check why this crap is always empty...

  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    // TODO fixme
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

export default VernacProof;
