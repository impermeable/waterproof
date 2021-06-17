/* eslint-disable require-jsdoc */
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

class VernacAssumption extends CoqType implements Visitable {
  discharge: string[];
  inline: string;

  constructor( array ) {
    super();
    this.discharge = array[1];
    this.inline = array[2];
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacAssumption(this);
  }
}

export default VernacAssumption;
