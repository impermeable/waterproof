import ASTVisitor from './visitor/ASTVisitor';

/**
 * Abstract class representing a generic type returned by SerApi
 */
export default abstract class CoqType implements Visitable {
  // eslint-disable-next-line @typescript-eslint/no-unused-vars
  abstract pprint() : string; // TODO add parameter indent.

  // eslint-disable-next-line require-jsdoc
  // flatten(): [[LocInfo, string]] | [] {
  //   return [];
  // }
  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor): void {
    // throw new Error('Method not implemented.');
    visitor.visitCoqType(this);
  }
}

export interface Visitable {
  accept(visitor: ASTVisitor) : void;
}
