/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
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
    const list = array[2];
    this.data = [];
    for (let i = 0; i < list.length; i++) {
      if (Array.isArray(list[i][3])) {
        if (list[i][3].length > 0) {
          this.data.push(convertToASTComp(list[i][3]));
        }
      }
    }
  }
  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0) {
    // const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    for (let i = 0; i < this.data.length; i++) {
      output = output.concat(this.cprint(this.data[i], indent));
    }
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacExtend(this);
    console.log(this.data);

    this.data.forEach((item) => {
      if (!Array.isArray(item)) {
        item.accept(visitor);
      }
    });
  }
}

export default VernacExtend;
