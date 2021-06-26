import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacCall object.
 */
class TacCall extends CoqType {
  content: any;
  locinfo: LocInfo;
  reference: any;

  /**
   * Constructor for TacCall type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(['loc', array[1]['loc'][0]]);
    this.content = convertToASTComp(array[1]['v'][0]['v']);
    if ('Reference' in array[1]['v'][1]) {
      const content = convertToASTComp(array[1]['v'][1]['Reference']['v']);
      const location = new LocInfo(['loc',
        array[1]['v'][1]['Reference']['loc'][0]]);
      this.reference = [location, content];
    } else {
      this.reference = [];
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
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1));
    output = output.concat(this.cprint(this.content, indent));
    if (this.reference.length > 0) {
      output = output.concat('Reference: ', tab);
      output = output.concat('\tLoc', this.reference[0].pprint(indent+2));
      output = output.concat(this.cprint(this.reference[1], indent+1));
    }
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitTacCall(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(v);
    }
  }
}

export default TacCall;
