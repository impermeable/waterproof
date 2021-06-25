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
    this.data = array.slice(1);
    this.data.forEach((items) => {
      console.warn('items', items);
      if (Array.isArray(items[0])) {
        items.forEach((e) => {
          e = convertToASTComp(e);
        });
      } else {
        items = convertToASTComp(items);
      }
    });
  }
  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
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

export class GenArg extends CoqType implements Visitable {
  level: string;
  optArgs: [];

  constructor( array ) {
    super(array);
    this.level = array[1];
    this.optArgs = array[2];
  }
}

export class VernacSolve extends CoqType implements Visitable {
  data: any;

  constructor( array ) {
    super(array);
    this.data = array.slice();
  }
}

export default VernacExtend;
