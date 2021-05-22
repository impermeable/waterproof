import CoqType from './CoqType';

/**
 * Class to represent a Coq CPrim type
 * CPrim = Signed Integer | String
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-prim_token
 */
// eslint-disable-next-line require-jsdoc
export default class CPrim extends CoqType {
  isNumeric: boolean;
  value: string | Record<string, unknown>;
  // eslint-disable-next-line require-jsdoc
  constructor( array : string | ['Number' | [string,
    Record<string, unknown>]] ) {
    super();
    console.warn('CPrim', array);
    this.isNumeric = array[1][0] === 'Numeric';
    if (this.isNumeric) {
      const {exp, frac, int} = array[1][1][1];
      const positive = array[1][1][0] === 'SPlus';
      /**
       * TODO: represent the number based on the 3 possible formats.
       * integer part: [0-9][0-9_]*
       * fractional part: empty or .[0-9_]+
       * exponent part: empty or [eE][+-]?[0-9][0-9_]* or
      */
      this.value = {positive: positive, exp: exp, frac: frac, int: int};
    } else {
      this.value = array[1][1];
    }
  }

  /**
   * Returns a nice pretty-printed expression of {VernacEndProof}
   * TODO: implement me
   */
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
