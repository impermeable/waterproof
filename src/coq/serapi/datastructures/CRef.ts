import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

// eslint-disable-next-line require-jsdoc
class CRef extends CoqType {
  libNames: { locinfo: any; content: any; };
  instanceExpr: any;
  // eslint-disable-next-line require-jsdoc
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

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Loc: ', this.libNames.locinfo.pprint(indent+1),
        tab);
    output = output.concat(this.cprint(this.libNames.content, indent));
    output = output.concat('Instance: ', this.instanceExpr.toString(), tab);
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
    visitor.visitCRef(this);
  }
}

export default CRef;
