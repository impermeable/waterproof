/**
 * For a given string, convert an index in terms of bytes (as often
 * provided by serapi) to an index in terms of a string
 * @param {String} str The string to perform the conversion for
 * @param {Number} byteIndex The index in terms of bytes
 * @return {Number} The index in the string corresponding to the
 * given byte, or -1 if it cannot be found
 */
function byteIndexToStringIndex( str, byteIndex ) {
  for (let j = Math.floor(byteIndex / 2); j<= byteIndex; j++) {
    if (Buffer.byteLength(str.slice(0, j)) === byteIndex) {
      return j;
    }
  }
  return -1;
}

export {
  byteIndexToStringIndex,
};
