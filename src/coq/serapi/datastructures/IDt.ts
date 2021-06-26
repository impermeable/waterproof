import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq IDt object.
 */
class IDt extends CoqType {
  name: any;

  /**
   * Constructor for IDt type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    if (typeof array[1] === 'string') {
      this.name = array[1];
    } else {
      this.name = array[1][1];
    }
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
    output = output.concat('Name: ', this.name.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) : void {
    visitor.visitIDt(this);
  }
}

export default IDt;
