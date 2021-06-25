import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

// eslint-disable-next-line require-jsdoc
class VernacOpenCloseScope extends CoqType implements Visitable {
  open: boolean;
  scope: string;

  /**
   *
   * @param {*} array
   */
  constructor( array ) {
    super(array);
    this.open = ('true' === array[1].toString());
    this.scope = array[2];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0) {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Open: ', this.open.toString(), tab);
    output = output.concat('Scope: ', this.scope, tab);
    return this.sprintf(super.pprint(indent), output);
  }

  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacOpenCloseScope(this);
  }
}

export default VernacOpenCloseScope;
