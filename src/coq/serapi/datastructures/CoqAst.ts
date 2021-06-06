import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to record the AST given back by serAPI
 */
export default class CoqAST extends CoqType implements Visitable {
  locinfo: LocInfo;
  content: any;

  /**
   * Construct CoqAST object from array containing the
   * AST information given back by serAPI.
   * @param {*} array The array with the CoqAST information
   */
  constructor( array ) {
    super();
    // this.representation = convertSexpToString(array, 0, '');
    this.locinfo = new LocInfo(array[1][1]);
    this.content = convertToASTComp(array[1][0]);
  }

  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor): void {
    // throw new Error('Method not implemented.');
    visitor.visitCoqAST(this);
    (this.content).accept(visitor);
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    return `(${this.constructor.name}\n\t(TODO)\n)\n`;
  }

  // eslint-disable-next-line require-jsdoc
  // flatten() : [[LocInfo, string]] | [] {
  //   return [];
  //   // if(this.content !== null){

  //   // }
  // }
}
