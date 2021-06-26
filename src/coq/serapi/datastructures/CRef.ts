import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq CRef object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CRef
 */
class CRef extends CoqType {
  libNames: { locinfo: any; content: any; };
  instanceExpr: any;

  /**
   * Constructor for CRef type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.libNames = {
      locinfo: new LocInfo(['loc', array[1].loc]),
      content: convertToASTComp(array[1].v),
    };
    if (Object.keys(array[2]).length > 0) {
      console.warn('Still need to parse this...');
    }
    this.instanceExpr = array[2];
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
    output = output.concat('Loc: ', this.libNames.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.libNames.content, indent));
    output = output.concat('Instance: ', this.instanceExpr.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitCRef(this);
  }
}

export default CRef;
