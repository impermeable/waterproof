import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacIntroPattern object.
 */
class TacIntroPattern extends CoqType {
  content: any;
  locinfo: any;

  /**
   * Constructor for TacIntroPattern type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.content = [];
    this.locinfo = [];
    for (let i = 0; i < array[2].length; i++) {
      this.content.push(convertToASTComp(array[2][i]['v']));
      this.locinfo.push(new LocInfo(['loc', array[2][i]['loc'][0]]));
    }
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    let output = '';
    for (let i = 0; i < this.content.length; i++) {
      output = output.concat('Loc: ', this.locinfo[i].pprint(indent+1));
      output = output.concat(this.cprint(this.content[i], indent));
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
    v.visitTacIntroPattern(this);
    for (let i = 0; i < this.content.length; i++) {
      if (!Array.isArray(this.content[i])) {
        (this.content[i]).accept(v);
      }
    }
  }
}

/* istanbul ignore next */
export default TacIntroPattern;
