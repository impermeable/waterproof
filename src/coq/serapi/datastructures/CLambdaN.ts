import {convertToASTComp, extractCoqAST} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq CLambdaN object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CLambdaN
 */
class CLambdaN extends CoqType {
  localExprs: any;
  expr: { locinfo: LocInfo; content: any; };

  /**
   * Constructor for VeracStartTheoremProof type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
    this.localExprs = array[1].map((el) => extractCoqAST(el));
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
  pprint(indent = 1): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    if (!this.localExprs === null) {
      for (let i = 0; i < this.localExprs.length; i++) {
        output = output.concat(this.localExprs[i].pprint(indent + 1), tab);
      }
    }
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent+1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) : void {
    visitor.visitCLambdaN(this);
  }
}

/* istanbul ignore next */
export default CLambdaN;
