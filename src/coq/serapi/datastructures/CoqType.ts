import ASTVisitor from './visitor/ASTVisitor';

/**
 * Abstract class representing a generic type returned by SerApi
 */
abstract class CoqType implements Visitable {
  /**
   * Constructor for abstract Coq type.
   * @param {Array} array Array to prarse.
   */
  constructor(array) {
    if (!Array.isArray(array)) {
      throw new TypeError(
          `Wrong arguments provided to ${this.constructor.name}`);
    }
  }

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent));
    let output = tab.concat(`(${this.constructor.name})`, tab);
    output = output.concat('\t(%s)', tab);
    return output;
  }

  /**
   * Replaces the ith %s in format with args[i] for each i
   * @param {string} format A string with %s appearing args.length times
   * @param {...string} args list of string arguments to put in place of %s
   * @return {string} format with each %s repalced by an element in args
   */
  sprintf(format, ...args): string {
    let i = 0;
    if (args.length === 0) {
      return format;
    }
    let skip = false;
    return format.replace(/%s/g, function() {
      if (!skip && args[i] !== undefined) {
        return args[i++];
      } else {
        skip = true;
        return '%s';
      }
    });
  }

  /**
   * Returns the pretty printer string for the Coq type child in content
   * @param {CoqType|Array} content A Coq type object or an array for an
   * unknown type
   * @param {number} indent The amount of indent needed in the output
   * @return {string} pretty printed Coq Type starting with 'Content'
   */
  cprint(content, indent): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = 'Content: ';
    if (!Array.isArray(content)) {
      output = output.concat(content.pprint(indent+1));
    } else {
      output = output.concat(tab, '\t', content.toString());
    }
    return output;
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitCoqType(this);
  }
}

/**
 * Visitable interface, implemented
 * by all traverse-able subtypes of {CoqType}
 */
export interface Visitable {
  accept(visitor: ASTVisitor) : void;
}

export default CoqType;
