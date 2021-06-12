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
    super();
    const {attrs, control, expr} = flatten(array[1]);

    this.attributes = {'attrs': attrs, 'control': control};
    // this.data = convertToASTComp(expr);
    this.data = convertToASTComp(expr);
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0) {
    const s = this.data != null ? this.data.pprint(indent+1) : '';
    // NOTE: we want an unscrict check here
    return super.sprintf(super.pprint(indent), s);
  }

  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor) : void {
    if (Array.isArray(this.data)) return;
    this.data.accept(visitor);
  }
}

export default GenericVType;
