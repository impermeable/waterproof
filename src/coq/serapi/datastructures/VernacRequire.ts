/* eslint-disable require-jsdoc */
/* eslint-disable camelcase */
import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to represent a Coq VernacRequire type.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacRequire
 */
class VernacRequire extends CoqType implements Visitable {
  qualid: any;
  export_flag: boolean;
  list: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super(array);
    // console.log('VernacRequire', (JSON.stringify(array[3])));
    this.qualid = array[1];
    this.export_flag = array[2] === 'true';
    this.list = array[3].map((el) => {
      return {
        locinfo: new LocInfo(['loc', el.loc]),
        content: convertToASTComp(el.v),
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
    output = output.concat('Qualid: ', this.qualid.toString(), tab);
    output = output.concat('Flag: ', this.export_flag.toString(), tab);
    for (let i = 0; i < this.list.length; i++) {
      output = output.concat('Loc: ', this.list[i].locinfo.pprint(indent+1),
          tab);
      output = output.concat(this.cprint(this.list[i].content, indent));
    }
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacRequire(this);
  }
}

export default VernacRequire;
