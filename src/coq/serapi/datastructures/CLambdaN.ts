/* eslint-disable require-jsdoc */
import {convertToASTComp, extractCoqAST} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CLambdaN
 */
class CLambdaN extends CoqType {
  localExprs: any;
  expr: { locinfo: LocInfo; content: any; };
  constructor( array ) {
    super(array);
    this.localExprs = array[1].map((el) => extractCoqAST(el));
    this.expr = {
      locinfo: new LocInfo(['loc', array[2].loc]),
      content: convertToASTComp(array[2].v),
    };
  }

  pprint(indent = 1): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    if (!this.localExprs === null) {
      for (let i = 0; i < this.localExprs.length; i++) {
        output = output.concat(this.localExprs[i].pprint(indent + 1), tab);
      }
    }
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent+1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }
}

export default CLambdaN;
