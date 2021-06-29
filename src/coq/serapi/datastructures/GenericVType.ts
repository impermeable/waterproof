import {convertToASTComp} from '../ASTProcessor';
import {flatten} from '../flatten-expr';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq GenericVType object.
 */
class GenericVType extends CoqType implements Visitable {
  attributes: { attrs: any; control: any; };
  data: any;

  /**
   * Constructor for GenericVType type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    const {attrs, control, expr} = flatten(array[1]);

    this.attributes = {'attrs': attrs, 'control': control};
    this.data = convertToASTComp(expr);
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
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
    if (!Array.isArray(this.data)) {
      this.data.accept(visitor);
    }
  }
}

/* istanbul ignore next */
export default GenericVType;
