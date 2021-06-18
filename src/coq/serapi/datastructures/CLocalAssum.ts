/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

class CLocalAssum extends CoqType {
  names: any;
  binderKind: any;
  expr: { locinfo: LocInfo; content: any; };

  constructor( array ) {
    super(array);
    console.warn('CLocalAssum', array);
    this.names = array[1].map((name) => ({
      locinfo: new LocInfo(['loc', name.loc]),
      content: convertToASTComp(name.v),
    }));
    this.binderKind = array[2];
    this.expr = {
      locinfo: new LocInfo(['loc', array[3].loc]),
      content: convertToASTComp(array[3].v),
    };
  }

  accept(v: ASTVisitor): void {
    v.visitCLocalAssum(this);
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    for (let i = 0; i < this.names.length; i++) {
      output = output.concat('Loc: ', this.names[i].locinfo.pprint(indent + 1),
          tab);
      output = output.concat(this.cprint(this.names[i].content, indent));
    }
    output = output.concat('Kind: ', this.binderKind, tab);
    output = output.concat('Loc: ', this.expr.locinfo.pprint(indent + 1), tab);
    output = output.concat(this.cprint(this.expr.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }
}

export default CLocalAssum;
