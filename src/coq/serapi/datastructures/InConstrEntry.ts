import CoqType from './CoqType';

/**
 * Class to represent a Coq InConstrEntry type
 * @see https://coq.github.io/doc/v8.11/api/coq/Constrexpr/index.html#type-notation_entry
 */
export default class InConstrEntry extends CoqType {
  data: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    this.data = array[1];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
