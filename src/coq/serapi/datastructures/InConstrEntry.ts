import CoqType from './CoqType';

/**
 * Class to represent a Coq InConstrEntry type
 * @see https://coq.github.io/doc/v8.11/api/coq/Constrexpr/index.html#type-notation_entry
 */
class InConstrEntry extends CoqType {
  data: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super(array);
    this.data = array[1];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Data: ', this.data.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }
}

export default InConstrEntry;
