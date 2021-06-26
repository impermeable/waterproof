import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacArg object.
 */
class TacArg extends CoqType {
  content: any;
  locinfo: LocInfo;

  /**
   * Constructor for TacArg type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(['loc', array[1]['loc'][0]]);
    this.content = convertToASTComp(array[1]['v']);
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    let output = '';
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1));
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitTacArg(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(v);
    }
  }
}

export default TacArg;
