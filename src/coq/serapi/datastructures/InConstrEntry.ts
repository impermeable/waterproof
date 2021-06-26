import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to represent a Coq InConstrEntry type
 * @see https://coq.github.io/doc/v8.11/api/coq/Constrexpr/index.html#type-notation_entry
 */
class InConstrEntry extends CoqType {
  data: any;

  /**
   * Constructor for InConstrEntry type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.data = array[1];
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Data: ', this.data.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) {
    visitor.visitInConstrEntry(this);
  }
}

export default InConstrEntry;
