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

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
