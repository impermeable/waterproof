/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

class TacReduce extends CoqType {
  type: string;
  content: any;
  locinfo: LocInfo;

  constructor( array ) {
    super(array);
    this.type = array[1][0];
    this.locinfo = new LocInfo(['loc',
      array[1][1]['AllOccurrences']['loc'][0]]);
    this.content = convertToASTComp(array[1][1]['AllOccurrences']['v'][1]['v']);
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Type: ', this.type, tab);
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitTacReduce(this);
    (this.content).accept(v);
  }
}

export default TacReduce;
