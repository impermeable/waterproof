import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq KerName object.
 */
class KerName extends CoqType {
  Id: string;
  type: string;

  /**
   * Constructor for KerName type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    const temp = array[2][1].toString().split('#');
    this.Id = temp[temp.length - 1].replace(/_/g, '');
    this.type = temp[0].replace(/_/g, ' ');
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
    output = output.concat('Id: ', this.Id, tab);
    output = output.concat('Type: ', this.type, tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitKerName(this);
  }
}

/* istanbul ignore next */
export default KerName;
