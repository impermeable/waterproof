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

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Strings: ', this.strings, tab);
    if (!Array.isArray(this.hintExpr)) {
      output = output.concat('Hint: ', this.hintExpr.pprint(indent+1), tab);
    } else {
      output = output.concat('Hint: ', tab, '\t', this.hintExpr.toString(),
          tab);
    }
    return this.sprintf(super.pprint(indent), output);
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacHints(this);
  }
}
