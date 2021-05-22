/* eslint-disable camelcase */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * Class to represent a Coq VernacRequire type.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacRequire
 */
export default class VernacRequire extends CoqType {
  qualid: any;
  export_flag: boolean;
  list: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    // console.log('VernacRequire', (JSON.stringify(array[3])));
    this.qualid = array[1];
    this.export_flag = array[2] === 'true';
    this.list = array[3].map((el) => {
      return {
        locinfo: new LocInfo(['loc', el.loc]),
        content: convertToASTComp(el.v),
      };
    });
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
