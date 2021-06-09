/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

export default class DefineBody extends CoqType {
  localExprList: any;
  rawRedExprOption: any;
  expr: { locinfo: LocInfo; content: any; };
  exprOption: any;

  constructor( array ) {
    super();
    this.localExprList = array[1];
    this.rawRedExprOption = array[2];
    this.expr = {
      locinfo: new LocInfo(['loc', array[3].loc]),
      content: convertToASTComp(array[3].v),
    };
    this.exprOption = array[4];
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Local expr: ', this.localExprList.toString(), tab);
    output = output.concat('Red exp: ', this.rawRedExprOption.toString(), tab);
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent + 1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    output = output.concat('Expr option: ', this.exprOption.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }
}
