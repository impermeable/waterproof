const flatten = require('./flatten-expr').flatten;

/**
 * The ppDict assigns to every name of an object appearing in an AST a function
 * that tells how to print that object
 */
const ppDict = {
  'CRef': printCRef,
  'TacAlias': printTacAlias,
  'TacGeneric': printTacGeneric,
  'VernacEndProof': printVernacEndProof,
  'VernacExpr': printVernacExpr,
  'VernacExtend': printVernacExtend,
  'VernacProof': printVernacProof,
  'VernacStartTheoremProof': printVernacStartTheoremProof,
  'CNotation': printCNotation,
  'CPrim': printCPrim,
};


/**
 * Recursive function to pretty-print the AST
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed sentence
 */
function prettyPrint( array, s ) {
  if ( array[0] in ppDict ) {
    return ppDict[array[0]](array, s);
  }
  return '';
}

/**
 * Pretty-print a CRef object
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printCRef( array, s ) {
  return 'Cref';
}

/**
 * Pretty-print the "VernacEndProof" object, such as 'Qed'
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printVernacEndProof( array, s ) {
  if ( array[1][0] === 'Proved' && array[1][1] === 'Opaque' ) {
    return 'Qed';
  }
  return '';
}

/**
 * Pretty-print the "VernacExpr" object,
 * often (always?) appears as the first object in the AST
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printVernacExpr( array, s ) {
  return prettyPrint( array[2], s );
}

/**
 * Pretty-print the "VernacExtend" object
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printVernacExtend( array, s ) {
  console.log(array);
  // TODO: implement
  return prettyPrint( array[2][2][3], s);
}

/**
 * Pretty-print the "VernacProof" object
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printVernacProof( array, s ) {
  return 'Proof';
}

/**
 * Pretty-print the "VernacStartTheoremProof" object,
 * this occurs in for instance "Theorem ref_test : 0 = 0."
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printVernacStartTheoremProof( array, s ) {
  return `${array[1]} ${array[2][0][0][0][0][1][1]}`
      + ` : ${prettyPrint(array[2][0][1][1][0][1])}`;
}

/**
 * Pretty-print the "CNotation" object
 * @param {Array} array The array to print
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printCNotation( array, s) {
  // TODO: code below only works for 2 occurences
  return array[1][1].replace('_', prettyPrint(array[2][0][0][0][1]))
      .replace('_', prettyPrint(array[2][0][1][0][1]));
}

/**
 * Pretty-print the CPrim Coq object
 * @param {Array} array Nested array with a CoqPrimitive object
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printCPrim( array, s) {
  console.log(array);
  return array[1][1];
}

/**
 * Pretty-print a TacAlias object. A TacAlias object
 * seems to correspond to a Tactic Notation object.
 * @param {Array} array Nested array with TacAlias object
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printTacAlias( array, s ) {
  return array[1][1][0][3][1].slice(0, -8)
      .replace('#', prettyPrint(array[1][1][1][0], s))
      .replace('#', prettyPrint(array[1][1][1][1], s));
}

/**
 * Pretty-print a TacGeneric object. Such an object
 * occurs for instance for what is in placeholders in
 * Tactic Notations
 * @param {Array} array The array with the TacGeneric object
 * @param {String} s A string to pass information
 * @return {String} The pretty-printed segment
 */
function printTacGeneric( array, s ) {
  if (array[1][2][1] === 'ident' ) {
    return array[1][3][1];
  } else if (array[1][2][1] === 'constr') {
    return prettyPrint(array[1][3][0][1], s);
  }
  return 'Unknown_TacGeneric';
}

/**
 * Toy function to traverse a nested array and log the
 * contents to the console
 * @param {Array} toTraverse The nested array to traverse
 */
function traverseArray( toTraverse ) {
  if (! Array.isArray(toTraverse) ) {
    console.log(toTraverse);
    return;
  }
  if ( toTraverse[0] !== 'loc') {
    for (const el of toTraverse) {
      traverseArray(el);
    }
  }
}

/**
 * Extract the part with the CoqAST information
 * from a nested Array parsed from a serAPI s-expression
 * @param {Array} nestedArrays The nested array to extract AST part from
 * @return {Object} A CoqAST object with the CoqAST information
 */
function extractCoqAST( nestedArrays ) {
  if ( Array.isArray(nestedArrays) ) {
    if ( nestedArrays[0] === 'CoqAst' ) {
      return new CoqAST(nestedArrays);
    }
    for ( const el of nestedArrays ) {
      const result = extractCoqAST( el );
      if ( result ) {
        return result;
      }
    }
  }
  return null;
}

/**
 * Convert a serialized expression, i.e. nested arrays as given
 * by serAPI, to JavaScript object. Intended for use for instance
 * in the constructors of such objects
 * @param {Array} array  The array with the serialized expression
 * @return {Object}  Either the JavaScript object representation the
 * serialized object, or else just the original array
 */
function convertToASTComp(array) {
  if (array[0] in constrDict) {
    const ConstructorForObject = constrDict[array[0]];
    return new ConstructorForObject(array);
  }
  return array;
}

/**
 * Class to record the AST given back by serAPI
 */
class CoqAST {
  /**
   * Construct CoqAST object from array containing the
   * AST information given back by serAPI.
   * @param {*} array The array with the CoqAST information
   */
  constructor( array ) {
    // this.representation = convertSexpToString(array, 0, '');
    this.locinfo = new LocInfo(array[1][1]);
    this.content = convertToASTComp(array[1][0]);
  }
}
/*

/!** Convert an s-expression to a string with indentation *!/
function convert_s_exp_to_string( expr, depth, stringSoFar ) {
  let returnString = stringSoFar;
  if (Array.isArray(expr)) {
    for (let i = 0; i < expr.length; i++) {
      returnString = convert_s_exp_to_string(expr[i], depth + 1, returnString);
    }
    return returnString;
  }
  return returnString + '\n' + '| '.repeat((depth)) + expr.toString();
}
*/

/**
 * A JavaScript equivalent of a VernacExpr object
 */
class VernacExpr {
  /**
   * Construct a VernacExpr objected from a nested array
   * with the representation of the object.
   * @param {Array} array Array as parsed from SerAPI message
   */
  constructor( array ) {
    // console.log('In the constructor of VernacExpr...');
    this.data = array;
    this.data[2] = convertToASTComp(array[2]);
    this.content = this.data[2];
  }
}

/**
 * A JavaScript equivalent of a Coq VernacExtend object
 */
class VernacExtend {
  /**
   * Construct a VernacExtend object from a nested array
   * with the representation of the object
   * @param {Array} array Array as parsed from SerAPI message
   */
  constructor( array ) {
    // console.log('In the constructor of VernacExtend...');
    this.data = array;
  }
}

/**
 * Class to record location info that is often part
 * of an AST given back by serAPI.
 */
class LocInfo {
  /**
   * Construct a LocInfo object from an array containing
   * serAPI location info
   * @param {Array} array Array containing location info
   */
  constructor( array ) {
    const result = flatten(array)[1][0];
    this.fname = result.fname;
    this.line_nb = result.line_nb;
    this.bol_pos = result.bol_pos;
    this.line_nb_last = result.line_nb_last;
    this.bol_pos_last = result.bol_pos_last;
    this.bp = result.bp;
    this.ep = result.ep;
  }
}

const constrDict = {
  'VernacExpr': VernacExpr,
  'VernacExtend': VernacExtend,
};

export {
  traverseArray,
  extractCoqAST,
  CoqAST,
  prettyPrint,
};
