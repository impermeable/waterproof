/* eslint-disable require-jsdoc */
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

class KerName extends CoqType {
//   MPfile: any;
  Id: string;
  type: string;

  constructor( array ) {
    super(array);
    const temp = array[2][1].toString().replaceAll('_', '').split('#');
    this.Id = temp[temp.length - 1];
    this.type = temp[0];
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    // output = output.concat('MPfile: ', this.MPfile.toString(), tab);
    output = output.concat('Id: ', this.Id, tab);
    output = output.concat('Type: ', this.type, tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitKerName(this);
  }
}

export default KerName;
