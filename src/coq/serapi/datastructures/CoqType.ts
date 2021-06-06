import LocInfo from './LocInfo';

/**
 * Abstract class representing a generic type returned by SerApi
 */
export default abstract class CoqType {
  abstract pprint() : string; // TODO add parameter indent.

  // eslint-disable-next-line require-jsdoc
  flatten(): [[LocInfo, string]] | [] {
    return [];
  }
}
