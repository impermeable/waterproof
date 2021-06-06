/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

export default class VernacHints extends CoqType implements Visitable {
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

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacHints(this);
  }
}
