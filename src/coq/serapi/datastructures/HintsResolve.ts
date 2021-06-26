import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq HintsResolve object.
 */
class HintsResolve extends CoqType {
  hintList: any;

  /**
   * Constructor for HintsResolve type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.hintList = array[1].map((el) => {
      return {
        info: el[0],
        bool: el[1] === 'true',
        refOrConstr: convertToASTComp(el[2]),
      };
    });
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    this.hintList.forEach((hint) => {
      output = output.concat(`Hint: ${hint.info}
          ${hint.refOrConstr.pprint(indent+1)}`, tab);
    });
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor) : void {
    v.visitHintsResolve(this);
  }
}

/**
 * A JavaScript equivalent of a Coq HintsResolve object.
 */
export class HintsReference extends CoqType {
  locinfo: any;
  content: any;

  /**
   * Constructor for HintsReference type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.locinfo = new LocInfo(['loc', array[1].loc]);
    this.content = convertToASTComp(array[1].v);
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1), tab);
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
    v.visitHintsReference(this);
  }
}

export default HintsResolve;
