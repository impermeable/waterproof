/* eslint-disable require-jsdoc */
import {convertToASTComp, extractCoqAST} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CLambdaN
 */
export default class CLambdaN extends CoqType {
  localExprs: any;
  expr: { locinfo: LocInfo; content: any; };
  constructor( array ) {
    super();
    this.localExprs = array[1].map((el) => extractCoqAST(el));
    this.expr = {
      locinfo: new LocInfo(['loc', array[2].loc]),
      content: convertToASTComp(array[2].v),
    };
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
