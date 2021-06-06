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

  pprint(): string {
    throw new Error('Method not implemented.');
  }

  accept(visitor: ASTVisitor): void {
    visitor.visitVernacProof(this);
  }
}
