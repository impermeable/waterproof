/**
 * Abstract class representing a generic type returned by SerApi
 */
export default abstract class CoqType {
  abstract pprint() : string; // TODO add parameter indent.
}
