/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/** Represents the Coq CProdN type
 *  CProdN = local_binder_expr list * constr_expr
 */
export default class CProdN extends CoqType {
  localExprs: [CoqType];
  expr: { locinfo: LocInfo; content: any; };

  constructor( array ) {
    super();
    console.warn('CProdN', array);
    this.localExprs = array[1].map((e) => convertToASTComp(e));
    this.expr = {
      locinfo: new LocInfo(['loc', array[2].loc]),
      content: convertToASTComp(array[2].v),
    };
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
