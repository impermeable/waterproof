/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

class TacCall extends CoqType {
  content: any;
  locinfo: LocInfo;
  reference: any;

  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(['loc', array[1]['loc'][0]]);
    this.content = convertToASTComp(array[1]['v'][0]['v']);
    if ('Reference' in array[1]['v'][1]) {
      const content = convertToASTComp(array[1]['v'][1]['Reference']['v']);
      const location = new LocInfo(['loc',
        array[1]['v'][1]['Reference']['loc'][0]]);
      this.reference = [location, content];
    } else {
      this.reference = [];
    }
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1));
    output = output.concat(this.cprint(this.content, indent));
    if (this.reference.length > 0) {
      output = output.concat('Reference: ', tab);
      output = output.concat('\tLoc', this.reference[0].pprint(indent+2));
      output = output.concat(this.cprint(this.reference[1], indent+1));
    }
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitTacCall(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(v);
    }
  }
}

export default TacCall;
