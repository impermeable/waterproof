/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

class TacApply extends CoqType {
  arg1: boolean;
  arg2: boolean;
  content: any;
  locinfo: LocInfo;

  constructor( array ) {
    super(array);
    this.arg1 = ('true' === array[1].toString());
    this.arg2 = ('true' === array[2].toString());
    this.locinfo = new LocInfo(['loc', array[3][0][1][0]['loc'][0]]);
    this.content = convertToASTComp(array[3][0][1][0]['v']);
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitTacApply(this);
  }
}

export default TacApply;
