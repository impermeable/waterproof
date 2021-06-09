import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/* eslint-disable require-jsdoc */
export default class VernacProof extends CoqType implements Visitable {
  sectionSubsetExpr: any;
  rawGenericArg: any;
  // TODO: check why this crap is always empty...

  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    // TODO fixme
    super();
    this.rawGenericArg = array[0] || {};
    this.sectionSubsetExpr = array[1] || {};
  }

  pprint(indent = 0) {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Arg: ', this.rawGenericArg.toString(), tab);
    output = output.concat('Expr: ', this.sectionSubsetExpr.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacProof(this);
  }
}
