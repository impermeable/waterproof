import VernacEndProof from './datastructures/VernacEndProof';
import CPrim from './datastructures/CPrim';
import CNotation from './datastructures/CNotation';
import VernacRequire from './datastructures/VernacRequire';
import SerQualid from './datastructures/SerQualid';
import InConstrEntry from './datastructures/InConstrEntry';
import CRef from './datastructures/CRef';
import VernacStartTheoremProof from './datastructures/VernacStartTheoremProof';
import CProdN from './datastructures/CProdN';
import CApp from './datastructures/CApp';
import CLocalAssum from './datastructures/CLocalAssum';
import IDt from './datastructures/IDt';
import VernacDefinition from './datastructures/VernacDefinition';
import DefineBody from './datastructures/DefineBody';
import CLambdaN from './datastructures/CLambdaN';
import VernacHints from './datastructures/VernacHints';
import HintsResolve, {HintsReference} from './datastructures/HintsResolve';
import CoqAST from './datastructures/CoqAst';
import VernacExpr from './datastructures/VernacExpr';
import VernacExtend, {GenArg, VernacSolve} from './datastructures/VernacExtend';
import VernacProof from './datastructures/VernacProof';
import GenericVType from './datastructures/GenericVType';
import VernacAssumption from './datastructures/VernacAssumption';

import VernacOpenCloseScope from './datastructures/VernacOpenCloseScope';
// import TacAlias from './dataqstructures/TacAlias';
import TacAlias from './datastructures/TacAlias';
import TacAtom from './datastructures/TacAtom';
import KerName from './datastructures/KerName';
import TacApply from './datastructures/TacApply';
import TacReduce from './datastructures/TacReduce';
import TacticDefinition from './datastructures/TacticDefinition';
import TacFun from './datastructures/TacFun';
import TacThen from './datastructures/TacThen';
import TacIntroPattern from './datastructures/TacIntroPattern';
import TacRewrite from './datastructures/TacRewrite';
import TacArg from './datastructures/TacArg';
import TacCall from './datastructures/TacCall';
import IntroNaming from './datastructures/IntroNaming';
import IntroIdentifier from './datastructures/IntroIdentifier';

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
  return `${array[1]} ${array[2][0][0][0][0][1][1]}` +
      ` : ${prettyPrint(array[2][0][1][1][0][1])}`;
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
    if (currentlyNotParsedTypes.has(constrDict)) {
      currentlyNotParsedTypes.delete(constrDict);
    }
    try {
      const ConstructorForObject = constrDict[array[0]];
      return new ConstructorForObject(array);
    } catch (e) {
      // TODO: investigate
      if (array[0] === 'VernacDefinition') {
        return new VernacDefinition(array);
      }
    }
  } else {
    console.warn(`Currently not parsing: ${array[0]}`,
        JSON.parse(JSON.stringify(array.length > 1 ? array.slice(1) : array)));
    if (!currentlyNotParsedTypes.has(array[0])) {
      currentlyNotParsedTypes.set(array[0], 1);
    } else {
      currentlyNotParsedTypes.set(array[0],
          currentlyNotParsedTypes.get(array[0]) + 1);
    }
  }
  return array;
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


const constrDict = {
  'VernacExpr': VernacExpr,
  'VernacExtend': VernacExtend,
  'v': GenericVType,
  'VernacRequire': VernacRequire,
  'Ser_Qualid': SerQualid,
  'VernacStartTheoremProof': VernacStartTheoremProof,
  'VernacProof': VernacProof,
  'VernacEndProof': VernacEndProof,
  'CNotation': CNotation,
  'InConstrEntry': InConstrEntry,
  'CRef': CRef,
  'CPrim': CPrim,
  'CProdN': CProdN,
  'CApp': CApp,
  'CLocalAssum': CLocalAssum,
  'Name': IDt,
  'DefineBody': DefineBody,
  'CLambdaN': CLambdaN,
  'VernacHints': VernacHints,
  'HintsResolve': HintsResolve,
  'HintsReference': HintsReference,
  'VernacAssumption': VernacAssumption,
  'GenArg': GenArg,
  'VernacSolve': VernacSolve,
  'TacAlias': TacAlias,
  'VernacOpenCloseScope': VernacOpenCloseScope,
  'KerName': KerName,
  'TacAtom': TacAtom,
  'TacApply': TacApply,
  'VernacDefinition': VernacDefinition,
  'TacReduce': TacReduce,
  'TacticDefinition': TacticDefinition,
  'TacFun': TacFun,
  'TacThen': TacThen,
  'TacIntroPattern': TacIntroPattern,
  'TacRewrite': TacRewrite,
  'TacArg': TacArg,
  'TacCall': TacCall,
  'IntroNaming': IntroNaming,
  'IntroIdentifier': IntroIdentifier,
};

// const currentlyNotParsedTypes = new Set();
const currentlyNotParsedTypes = new Map();

export {
  traverseArray,
  extractCoqAST,
  CoqAST,
  prettyPrint,
  currentlyNotParsedTypes,
  convertToASTComp,
};
