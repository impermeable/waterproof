/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

/**
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CApp
 */
class CApp extends CoqType {
  [x: string]: any;
  first: { projFlag: any; expr: { locinfo: LocInfo; content: any; }; };
  constructor( array ) {
    super(array);
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

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Project flag: ', this.first.projFlag, tab);
    output = output.concat('Loc: ', this.first.expr.locinfo.pprint(
        indent + 1), tab);
    output = output.concat(this.cprint(this.first.expr.content, indent));
    for (let i = 0; i < this.list.length; i++) {
      output = output.concat('Loc: ', this.list[i].locinfo.pprint(indent + 1),
          tab);
      output = output.concat(this.cprint(this.list[i].expr.content, indent));
    }
    return super.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }
}

export default CApp;
