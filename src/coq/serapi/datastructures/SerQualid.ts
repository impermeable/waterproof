/* eslint-disable require-jsdoc */
import CoqType from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to represent a Coq (SerApi) SerQualid type.
 * @see https://github.com/ejgallego/coq-serapi/blob/v8.13/serlib/ser_libnames.ml#L24
 */
class SerQualid extends CoqType {
  dirPath: any;
  id: any;
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super(array);
    this.dirPath = array[1][1];
    this.id = array[2][1];
  }

  // eslint-disable-next-line require-jsdoc
  pprint(indent = 0) : string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Path: ', this.dirPath.toString(), tab);
    output = output.concat('Id: ', this.id.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  accept(v: ASTVisitor) : void {
    v.visitSerQualid(this);
  }
}

export default SerQualid;
