import {convertToASTComp} from '../ASTProcessor';
import {flatten} from '../flatten-expr';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

// eslint-disable-next-line require-jsdoc
export default class GenericVType extends CoqType implements Visitable {
  attributes: { attrs: any; control: any; };
  data: any;
  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
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
  accept(visitor: ASTVisitor) : void {
    if (Array.isArray(this.data)) return;
    this.data.accept(visitor);
  }
}
