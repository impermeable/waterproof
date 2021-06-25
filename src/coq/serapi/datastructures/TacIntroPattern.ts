/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

class TacIntroPattern extends CoqType {
  content: any;
  locinfo: any;

  constructor( array ) {
    super(array);
    this.content = [];
    this.locinfo = [];
    for (let i = 0; i < array.length - 1; i++) {
      this.content.push(convertToASTComp(array[2][i+1]['v']));
      this.locinfo.push(new LocInfo(['loc', array[2][i+1]['loc'][0]]));
    }
  }

  pprint(indent = 0): string {
    // const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    for (let i = 0; i < this.content.length; i++) {
      output = output.concat('Loc: ', this.locinfo[i].pprint(indent+1));
      output = output.concat(this.cprint(this.content[i], indent));
    }
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitTacIntroPattern(this);
    for (let i = 0; i < this.content.length; i++) {
      if (!Array.isArray(this.content[i])) {
        (this.content[i]).accept(v);
      }
    }
  }
}

export default TacIntroPattern;
