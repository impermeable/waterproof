/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

class IntroNaming extends CoqType {
  content: any;

  constructor( array ) {
    super(array);
    this.content = [];
    for (let i = 0; i < array.length - 1; i++) {
      this.content.push(convertToASTComp(array[i+1]));
    }
  }

  pprint(indent = 0): string {
    // const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    for (let i = 0; i < this.content.length; i++) {
      output = output.concat(this.cprint(this.content[i], indent));
    }
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitIntroNaming(this);
    for (let i = 0; i < this.content.length; i++) {
      if (!Array.isArray(this.content[i])) {
        (this.content[i]).accept(v);
      }
    }
  }
}

export default IntroNaming;
