import CoqType from './CoqType';

/**
 * A JavaScript equivalent of a Coq CPrim object.
 * CPrim = Signed Integer | String
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-prim_token
 */
class CPrim extends CoqType {
  isNumeric: boolean;
  value: string | Record<string, unknown>;

  /**
   * Constructor for CPrim type.
   * @param {array} array Array to parse
   */
  constructor( array : string | ['Number' | [string,
    Record<string, unknown>]] ) {
    super(array);
    this.isNumeric = array[1][0] === 'Numeric';
    if (this.isNumeric) {
      const {exp, frac, int} = array[1][1][1];
      const positive = array[1][1][0] === 'SPlus';
      this.value = {positive: positive, exp: exp, frac: frac, int: int};
    } else {
      this.value = array[1][1];
    }
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Is numeric: ', this.isNumeric.toString(), tab);
    if (this.isNumeric) {
      output = output.concat('\tPositive: ', this.value['positive'].toString(),
          tab);
      output = output.concat('\tExp: ', this.value['exp'].toString(), tab);
      output = output.concat('\tFrac: ', this.value['frac'].toString(), tab);
      output = output.concat('\tInt: ', this.value['int'].toString(), tab);
    } else {
      output = output.concat('Value: ', this.value.toString(), tab);
    }
    return this.sprintf(super.pprint(indent), output);
  }
}

export default CPrim;
