import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/** A JavaScript equivalent of a Coq CProdN object.
 *  CProdN = local_binder_expr list * constr_expr
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CProdN
 */
class CProdN extends CoqType {
  localExprs: [CoqType];
  expr: { locinfo: LocInfo; content: any; };

  /**
   * Constructor for CProdN type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.localExprs = array[1].map((e) => convertToASTComp(e));
    this.expr = {
      locinfo: new LocInfo(['loc', array[2].loc]),
      content: convertToASTComp(array[2].v),
    };
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
    for (let i = 0; i < this.localExprs.length; i++) {
      output = output.concat('Local expr: ');
      if (!Array.isArray(this.localExprs[i])) {
        output = output.concat(
            this.localExprs[i].pprint(indent + 1), tab);
      } else {
        output = output.concat(tab, '\t', this.localExprs[i].toString(), tab);
      }
    }
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent + 1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor): void {
    v.visitCProdN(this);
  }
}

/* istanbul ignore next */
export default CProdN;
