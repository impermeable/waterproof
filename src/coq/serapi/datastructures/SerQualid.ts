import CoqType from './CoqType';

/**
 * Class to represent a Coq (SerApi) SerQualid type.
 * @see https://github.com/ejgallego/coq-serapi/blob/v8.13/serlib/ser_libnames.ml#L24
 */
export default class SerQualid extends CoqType {
  dirPath: any;
  id: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    this.dirPath = array[1][1];
    this.id = array[2][1];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0) : string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Path: ', this.dirPath.toString(), tab);
    output = output.concat('Id: ', this.id.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }
}
