import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacAssumption object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacAssumption
 */
class VernacAssumption extends CoqType implements Visitable {
  discharge: string[];
  inline: string;

  /**
   * Constructor for VernacAssumption type
   * @param {Array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.discharge = array[1];
    this.inline = array[2];
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0) {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Discharge: ', this.discharge.toString(), tab);
    output = output.concat('Inline: ', this.inline.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacAssumption(this);
  }
}

export default VernacAssumption;
