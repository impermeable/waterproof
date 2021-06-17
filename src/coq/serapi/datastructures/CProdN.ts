/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/** Represents the Coq CProdN type
 *  CProdN = local_binder_expr list * constr_expr
 */
class CProdN extends CoqType {
  localExprs: [CoqType];
  expr: { locinfo: LocInfo; content: any; };

  constructor( array ) {
    super(array);
    console.warn('CProdN', array);
    this.localExprs = array[1].map((e) => convertToASTComp(e));
    this.expr = {
      locinfo: new LocInfo(['loc', array[2].loc]),
      content: convertToASTComp(array[2].v),
    };
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    for (let i = 0; i < this.localExprs.length; i++) {
      output = output.concat('Local expr: ');
      if (!Array.isArray(this.localExprs[i])) {
        output = output.concat(
            this.localExprs[i].pprint(indent + 1), tab);
      } else {
        output = output.concat(tab, '\t', this.localExprs[i].toString(), tab);
      }
    }
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent + 1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }
}

export default CProdN;
