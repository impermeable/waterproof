/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';

export default class VernacHints extends CoqType {
  strings: any;
  hintExpr: any;
  constructor( array ) {
    super();
    console.log('VernacHints', array);
    this.strings = array[1];
    this.hintExpr = convertToASTComp(array[2]);
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
