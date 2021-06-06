/* eslint-disable require-jsdoc */
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacExtend object
 */
export default class VernacExtend extends CoqType implements Visitable {
  data: any;
  /**
   * Construct a VernacExtend object from a nested array
   * with the representation of the object
   * @param {Array} array Array as parsed from SerAPI message
   */
  constructor( array ) {
    super();
    // console.log('In the constructor of VernacExtend...');
    // TODO fixme - use convertToAstComp
    this.data = array;
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacExtend(this);
  }
}
