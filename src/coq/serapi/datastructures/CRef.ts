import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

// eslint-disable-next-line require-jsdoc
export default class CRef extends CoqType {
  libNames: { locinfo: any; content: any; };
  instanceExpr: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    this.libNames = {
      locinfo: new LocInfo(['loc', array[1].loc]),
      content: convertToASTComp(array[1].v),
    };
    if (Object.keys(array[2]).length > 0) {
      console.warn('Still need to parse this...');
    }
    this.instanceExpr = array[2];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
