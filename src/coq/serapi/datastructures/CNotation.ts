import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq CNotation object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CNotation
 */
class CNotation extends CoqType {
  notation: CoqType;
  constrNotationSubstitution: { exprListOfLists: any; patternExprs: any;
    binderExprsListOfLists: any; exprList: any[]; };

  /**
   * Construct a CNotation object.
   * @param {Array} array the array to be parsed
   */
  constructor( array ) {
    super(array);
    this.notation = convertToASTComp(array[2]);

    // object of type List<> * List<List> * List<patterns> * List<List<binder>>
    this.constrNotationSubstitution = {
      'exprListOfLists': array[3][1],
      'patternExprs': array[3][2],
      'binderExprsListOfLists': array[3][3],
      'exprList': [],
    };
    this.constrNotationSubstitution['exprList'] = array[3][0].map((el) => ({
      locinfo: new LocInfo(['loc', el.loc]),
      content: convertToASTComp(el.v),
    }));
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
    output = output.concat(this.cprint(this.notation, indent));
    for (let i = 0;
      i < this.constrNotationSubstitution['exprList'].length;
      i++) {
      output = output.concat('Loc: ',
          this.constrNotationSubstitution['exprList'][i].locinfo.pprint(
              indent+1), tab);
      output = output.concat(this.cprint(
          this.constrNotationSubstitution['exprList'][i].content, indent));
    }
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v: ASTVisitor): void {
    v.visitCNotation(this);
  }
}

export default CNotation;
