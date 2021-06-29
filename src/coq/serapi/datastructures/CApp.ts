/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * A JavaScript equivalent of a Coq CApp object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Constrexpr/index.html#type-constr_expr_r.CApp
 */
class CApp extends CoqType {
  list: { option: any, expr: { locinfo: LocInfo, content: any}}[];
  first: { projFlag: any; expr: { locinfo: LocInfo; content: any; }; };

  /**
   * Construct a CApp object.
   * @param {Array} array the array to be parsed
   */
  constructor( array ) {
    super(array);
    this.first = {
      projFlag: array[1][0],
      expr: {
        locinfo: new LocInfo(['loc', array[1][1].loc]),
        content: convertToASTComp(array[1][1].v),
      },
    };
    this.list = array[2].map((el) => {
      return {
        expr: {
          locinfo: new LocInfo(['loc', el[0].loc]),
          content: convertToASTComp(el[0].v),
        },
        option: el[1],
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
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Project flag: ', this.first.projFlag, tab);
    output = output.concat('Loc: ', this.first.expr.locinfo.pprint(
        indent + 1), tab);
    output = output.concat(this.cprint(this.first.expr.content, indent));
    for (let i = 0; i < this.list.length; i++) {
      output = output.concat('Loc: ', this.list[i].expr.locinfo
          .pprint(indent + 1), tab);
      output = output.concat(this.cprint(this.list[i].expr.content, indent));
    }
    return super.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} v the visitor requiring
   * access to content of the current type
   */
  accept(v : ASTVisitor): void {
    v.visitCApp(this);
  }
}

/* istanbul ignore next */
export default CApp;
