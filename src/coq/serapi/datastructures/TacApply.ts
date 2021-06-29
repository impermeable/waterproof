import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq TacApply object.
 */
class TacApply extends CoqType {
  arg1: boolean;
  arg2: boolean;
  content: any;
  locinfo: LocInfo;

  /**
   * Constructor for the TacApply type.
   * @param {Array} array Array to parse.
   */
  constructor( array ) {
    super(array);
    console.log('BUGGG', array);
    this.arg1 = ('true' === array[1].toString());
    this.arg2 = ('true' === array[2].toString());
    this.locinfo = new LocInfo(['loc', array[3][0][1][0]['loc']]);
    this.content = convertToASTComp(array[3][0][1][0]['v']);
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
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitTacApply(this);
    if (!Array.isArray(this.content)) {
      (this.content).accept(v);
    }
  }
}

/* istanbul ignore next */
export default TacApply;
