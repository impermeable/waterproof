/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a VernacExpr object
 */
class VernacExpr extends CoqType {
  content: any;
  /**
   * Construct a VernacExpr objected from a nested array
   * with the representation of the object.
   * @param {Array} array Array as parsed from SerAPI message
   */
  constructor( array ) {
    super(array);
    // TODO fixme
    // console.log('In the constructor of VernacExpr...');
    const data = array;
    data[2] = convertToASTComp(array[2]);
    this.content = data[2];
  }

  print(indent = 0) {
    const output = '';
    output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  accept(v: ASTVisitor): void {
    v.visitVernacExpr(this);
  }
}

export default VernacExpr;
