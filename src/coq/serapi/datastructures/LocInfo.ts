import CoqType from './CoqType';

const flatten = require('../flatten-expr').flatten;

/**
 * Class to record location info that is often part
 * of an AST given back by serAPI.
 */
class LocInfo extends CoqType {
  fname: string;
  lineNb: number;
  bolPos: number;
  lineNbLast: number;
  bolPosLast: number;
  bp: number;
  ep: number;

  /**
   * Construct a LocInfo object from an array containing
   * serAPI location info
   * @param {Array} array Array containing location info
   */
  constructor( array ) {
    super(array);

    let result;
    if (Array.isArray(array[1])) {
      result = flatten(array)[1][0];
    } else {
      result = array[1];
    }

    this.fname = result.fname;
    this.lineNb = result.line_nb;
    this.bolPos = result.bol_pos;
    this.lineNbLast = result.line_nb_last;
    this.bolPosLast = result.bol_pos_last;
    this.bp = result.bp;
    this.ep = result.ep;
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
    output = output.concat('Name: ', this.fname, tab);
    output = output.concat('Start line: ', this.lineNb.toString(), tab);
    output = output.concat('Start pos: ', this.bolPos.toString(), tab);
    output = output.concat('End line: ', this.lineNbLast.toString(), tab);
    output = output.concat('End pos: ', this.bolPosLast.toString(), tab);
    output = output.concat('Bp: ', this.bp.toString(), tab);
    output = output.concat('Ep: ', this.ep.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }
}

export default LocInfo;
