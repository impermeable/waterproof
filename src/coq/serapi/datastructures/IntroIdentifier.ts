/* eslint-disable require-jsdoc */
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

class IntroIdentifier extends CoqType {
  id: string;

  constructor( array ) {
    super(array);
    this.id = array[1][1].toString();
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Id: ', this.id, tab);
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(v: ASTVisitor) : void {
    v.visitIntroIdentifier(this);
  }
}

export default IntroIdentifier;
