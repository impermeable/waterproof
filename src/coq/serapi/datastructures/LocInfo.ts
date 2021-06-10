/* eslint-disable camelcase */
import CoqType from './CoqType';

const flatten = require('../flatten-expr').flatten;

/**
 * Class to record location info that is often part
 * of an AST given back by serAPI.
 */
class LocInfo extends CoqType {
  fname: string;
  line_nb: number;
  bol_pos: number;
  line_nb_last: number;
  bol_pos_last: number;
  bp: number;
  ep: number;
  /**
   * Construct a LocInfo object from an array containing
   * serAPI location info
   * @param {Array} array Array containing location info
   */
  constructor( array ) {
    super();
    const result = flatten(array)[1][0];
    this.fname = result.fname;
    this.line_nb = result.line_nb;
    this.bol_pos = result.bol_pos;
    this.line_nb_last = result.line_nb_last;
    this.bol_pos_last = result.bol_pos_last;
    this.bp = result.bp;
    this.ep = result.ep;
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Name: ', this.fname, tab);
    output = output.concat('Start line: ', this.line_nb.toString(), tab);
    output = output.concat('Start pos: ', this.bol_pos.toString(), tab);
    output = output.concat('End line: ', this.line_nb_last.toString(), tab);
    output = output.concat('End pos: ', this.bol_pos_last.toString(), tab);
    output = output.concat('Bp: ', this.bp.toString(), tab);
    output = output.concat('Ep: ', this.ep.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }
}

export default LocInfo;
