/**
 * Takes nested arrays as returned by the s-expression `parse()` method, and
 * 'flattens' it by turning each list of the form
 * ((opt1 val1)(op2 val2)) into an object
 * {
 *    "opt1": val1,
 *    "opt2": val2,
 * }
 *
 * @param {Array} data the array returned by the s-expression parser
 * @return {Object|Array} an object with the keys & values from the expression
 *   ((key1 val1)(key2 val2)..), or an array possibly containing such objects
 */
function flatten(data) {
  /**
   * @param {Array} obj a part of the parsed s-expression
   * @return {Boolean} true iff `obj` is an array of the form `['key', value]`
   *   where `key` is not a number
   */
  function isKeyValuePair(obj) {
    return Array.isArray(obj)
      && obj.length == 2
      && typeof (obj[0]) === 'string'
      && Number(obj[0]).toString() !== obj[0];
  }

  /**
   * @param {Array} obj a part of the parsed s-expression
   * @return {Boolean} true iff `obj` is a non-empty array where each element
   *  is a key-value pair as defined by `isKeyValuePair`
   */
  function isKeyValueList(obj) {
    return Array.isArray(obj) && obj.every(isKeyValuePair);
  }

  if (isKeyValueList(data)) {
    const obj = {};
    for (const [key, value] of data) {
      if (typeof value === 'string') {
        if (isNaN(value)) {
          obj[key] = value;
        } else {
          obj[key] = Number(value);
        }
      } else {
        obj[key] = flatten(value);
      }
    }
    return obj;
  } else if (Array.isArray(data)) {
    return data.map(flatten);
  } else {
    return data;
  }
}

export {
  flatten,
};
