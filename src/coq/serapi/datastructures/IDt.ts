/* eslint-disable require-jsdoc */
import CoqType from './CoqType';

export default class IDt extends CoqType {
  name: any;
  constructor( array ) {
    super();
    this.name = array[1];
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
