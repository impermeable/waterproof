import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to record the AST given back by serAPI
 */
class CoqAST extends CoqType implements Visitable {
  locinfo: LocInfo;
  content: any;

  /**
   * Construct CoqAST object from array containing the
   * AST information given back by serAPI.
   * @param {Array} array The array with the CoqAST information
   */
  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(array[1][1]);
    this.content = convertToASTComp(array[1][0]);
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
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1), tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitCoqAst(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(visitor);
    }
  }
}

/* istanbul ignore next */
export default CoqAST;
