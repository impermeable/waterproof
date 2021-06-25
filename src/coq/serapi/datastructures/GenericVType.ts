import {convertToASTComp} from '../ASTProcessor';
import {flatten} from '../flatten-expr';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

// eslint-disable-next-line require-jsdoc
class GenericVType extends CoqType implements Visitable {
  attributes: { attrs: any; control: any; };
  data: any;

  /**
   *
   * @param {*} array
   */
  constructor( array ) {
    super(array);
    const {attrs, control, expr} = flatten(array[1]);

    this.attributes = {'attrs': attrs, 'control': control};
    // this.data = convertToASTComp(expr);
    // console.log(expr);
    this.data = convertToASTComp(expr);
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0) {
    if (this.data == null) {
      console.warn('Cannot pprint this.data, see', this.data);
      return '';
    }
    try {
      const s = this.data.pprint(indent+1);
      return super.sprintf(super.pprint(indent), s);
    } catch {
      console.warn('Cannot pprint this.data, see', this.data);
      return '';
    }
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) : void {
    if (Array.isArray(this.data)) return;
    this.data.accept(visitor);
  }
}

export default GenericVType;
