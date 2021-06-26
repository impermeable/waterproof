import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacAlias object.
 */
class TacAlias extends CoqType {
  locinfo: LocInfo;
  content: any;

  /**
   * Constructor for TacAlias type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(['loc', array[1]['loc'][0]]);
    this.content = convertToASTComp(array[1]['v'][0]);
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
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) : void {
    visitor.visitTacAlias(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(visitor);
    }
  }
}

export default TacAlias;
