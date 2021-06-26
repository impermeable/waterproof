import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacFun object.
 */
class TacFun extends CoqType {
  content: any;
  name: string;

  /**
   * Constructor for TacFun type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.name = array[1][0]['Name'][1].toString();
    this.content = [];
    for (let i = 0; i < array[1].length - 1; i++) {
      this.content.push(convertToASTComp(array[1][i+1]));
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
    output = output.concat('Name: ', this.name, tab);
    for (let i = 0; i < this.content.length; i++) {
      output = output.concat(this.cprint(this.content[i], indent));
    }
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
    v.visitTacFun(this);
    for (let i = 0; i < this.content.length; i++) {
      if (!Array.isArray(this.content[i])) {
        (this.content[i]).accept(v);
      }
    }
  }
}

export default TacFun;
