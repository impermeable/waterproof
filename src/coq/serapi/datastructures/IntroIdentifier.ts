import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq IntroIdentifier object.
 */
class IntroIdentifier extends CoqType {
  id: string;

  /**
   * Constructor for IntroIdentifier type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.id = array[1][1].toString();
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
    output = output.concat('Id: ', this.id, tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitIntroIdentifier(this);
  }
}

export default IntroIdentifier;
