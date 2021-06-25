/* eslint-disable require-jsdoc */
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

class VernacAssumption extends CoqType implements Visitable {
  discharge: string[];
  inline: string;

  constructor( array ) {
    super(array);
    this.discharge = array[1];
    this.inline = array[2];
  }

  /**
   * allows the ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacAssumption(this);
  }
}

export default VernacAssumption;
