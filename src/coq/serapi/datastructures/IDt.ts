/* eslint-disable require-jsdoc */
import CoqType from './CoqType';

class IDt extends CoqType {
  name: any;
  constructor( array ) {
    super(array);
    this.name = array[1];
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Name: ', this.name.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }
}

export default IDt;
