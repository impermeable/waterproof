import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq VernacExtend object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacExtend
 */
class VernacExtend extends CoqType implements Visitable {
  data: any;

  /**
   * Construct for the VernacExtend type
   * @param {Array} array Array to parse
   */
  constructor( array ) {
    super(array);
    const list = array[2];
    this.data = [];
    for (let i = 0; i < list.length; i++) {
      if (Array.isArray(list[i][3])) {
        if (list[i][3].length > 0) {
          if (typeof list[i][3][0] === 'string') {
            this.data.push(convertToASTComp(list[i][3]));
          } else {
            this.data.push(convertToASTComp(list[i][3][0]));
          }
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

/* istanbul ignore next */
export default VernacExtend;
