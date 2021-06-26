import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacOpenCloseScope object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacOpenCloseScope
 */
class VernacOpenCloseScope extends CoqType implements Visitable {
  open: boolean;
  scope: string;

  /**
   * Constructor for the VernacOpenCloseScope tpye
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.open = ('true' === array[1].toString());
    this.scope = array[2];
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
    output = output.concat('Open: ', this.open.toString(), tab);
    output = output.concat('Scope: ', this.scope, tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacOpenCloseScope(this);
  }
}

export default VernacOpenCloseScope;
