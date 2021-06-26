import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacReduce object.
 */
class TacReduce extends CoqType {
  type: string;
  content: any;
  locinfo: LocInfo;

  /**
   * Constructor for TacReduce type.
   * @param {array} array Array to parse.
   */
  constructor( array ) {
    super(array);
    this.type = array[1][0];
    this.locinfo = new LocInfo(['loc',
      array[1][1]['AllOccurrences']['loc'][0]]);
    this.content = convertToASTComp(array[1][1]['AllOccurrences']['v'][1]['v']);
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
    output = output.concat('Type: ', this.type, tab);
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitTacReduce(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(v);
    }
  }
}

export default TacReduce;
