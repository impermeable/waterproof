import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq IntroNaming object.
 */
class IntroNaming extends CoqType {
  content: any;

  /**
   * Constructor for IntroNaming type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.content = [];
    for (let i = 0; i < array.length - 1; i++) {
      this.content.push(convertToASTComp(array[i+1]));
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
    v.visitIntroNaming(this);
    for (let i = 0; i < this.content.length; i++) {
      if (!Array.isArray(this.content[i])) {
        (this.content[i]).accept(v);
      }
    }
  }
}

/* istanbul ignore next */
export default IntroNaming;
