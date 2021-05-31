/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CApp
 */
export default class CApp extends CoqType {
  [x: string]: any;
  first: { projFlag: any; expr: { locinfo: LocInfo; content: any; }; };
  constructor( array ) {
    super();
    // TODO not really sure about these arguments
    this.first = {
      projFlag: array[1][0],
      expr: {
        locinfo: new LocInfo(['loc', array[1][1].loc]),
        content: convertToASTComp(array[1][1].v),
      },
    };
    this.list = array[2].map((el) => {
      return {
        expr: {
          locinfo: new LocInfo(['loc', el[0].loc]),
          content: convertToASTComp(el[0].v),
        },
        option: el[1],
      };
    });
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
