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

  /**
   * Parses an input array into a proper datastructure.
   * @param {Array} array: Array to parse
   */
  constructor( array ) {
    super(array);
    this.dirPath = array[1][1];
    this.id = array[2][1];
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0) : string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Path: ', this.dirPath.toString(), tab);
    output = output.concat('Id: ', this.id.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor) : void {
    visitor.visitSerQualid(this);
  }
}

export default SerQualid;
