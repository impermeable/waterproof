import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * Class to  represent a Coq CNotation type
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CNotation
 */
export default class CNotation extends CoqType {
  notation: CoqType;
  constrNotationSubstitution: { exprListOfLists: any; patternExprs: any;
    binderExprsListOfLists: any; exprList: never[]; };

  /**
   * Construct a CNotation object.
   * @param {Array} array the array to be parsed
   */
  constructor( array ) {
    // TODO not sure what array[1] is
    super();
    this.notation = convertToASTComp(array[2]);

    // object of type List<> * List<List> * List<patterns> * List<List<binder>>
    this.constrNotationSubstitution = {
      'exprListOfLists': array[3][1],
      'patternExprs': array[3][2],
      'binderExprsListOfLists': array[3][3],
      'exprList': [],
    };
    this.constrNotationSubstitution['exprList'] = array[3][0].map((el) => ({
      locinfo: new LocInfo(['loc', el.loc]),
      content: convertToASTComp(el.v),
    }));
    // this.notation = array[1];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
