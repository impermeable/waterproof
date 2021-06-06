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
  pprint() : string {
    throw new Error('Method not implemented.');
  }
}
