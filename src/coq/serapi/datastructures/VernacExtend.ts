/* eslint-disable require-jsdoc */
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacExtend object
 */
class VernacExtend extends CoqType implements Visitable {
  data: any;
  /**
   * Construct a VernacExtend object from a nested array
   * with the representation of the object
   * @param {Array} array Array as parsed from SerAPI message
   */
  constructor( array ) {
    super(array);
    // console.log('In the constructor of VernacExtend...');
    // TODO fixme - use convertToAstComp
    this.data = array;
  }

  pprint(indent = 0) {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Data: ', this.data.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacExtend(this);
  }
}

export default VernacExtend;
