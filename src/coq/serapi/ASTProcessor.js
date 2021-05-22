import VernacEndProof from './datastructures/VernacEndProof';
import CPrim from './datastructures/CPrim';

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
    const ConstructorForObject = constrDict[array[0]];
    return new ConstructorForObject(array);
  } else {
    console.warn(`Currently not parsing: ${array[0]}`,
        JSON.parse(JSON.stringify(array.length > 1 ? array.slice(1) : array)));
    if (!currentlyNotParsedTypes.has(array[0])) {
      currentlyNotParsedTypes.set(array[0], 1);
    } else {
      currentlyNotParsedTypes[array[0]]++;
    }
    // currentlyNotParsedTypes.add(array[0]);
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

// eslint-disable-next-line require-jsdoc
class GenericVType {
  /**
   *
   * @param {*} array
   */
  constructor( array ) {
    const {attrs, control, expr} = flatten(array[1]);

    this.attributes = {'attrs': attrs, 'control': control};
    // this.data = convertToASTComp(expr);
    this.data = convertToASTComp(expr);
  }
}

// eslint-disable-next-line require-jsdoc
class VernacRequire {
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    // console.log('VernacRequire', (JSON.stringify(array[3])));
    this.qualid = array[1];
    this.export_flag = array[2] === 'true';
    this.list = array[3].map((el) => {
      return {
        locinfo: new LocInfo(['loc', el.loc]),
        content: convertToASTComp(el.v),
      };
    });
  }
}

// eslint-disable-next-line require-jsdoc
class SerQualid {
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    this.dirPath = array[1][1];
    this.id = array[2][1];
  }
}

// eslint-disable-next-line require-jsdoc
class VernacStartTheoremProof {
  // TheoremKindEnum = {
  //   Theorem: 'Theorem',
  //   Lemma: 'Lemma',
  //   Fact: 'Fact',
  //   Remark: 'Remark',
  //   Property: 'Property',
  //   Proposition: 'Proposition',
  //   Corollary: 'Corollary',
  // }

  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    this.theoremKind = array[1];
    // console.log
    this.proofExprs = [];
    this.proofExprs = array[2][0].map((el) => {
      const id = el[0];
      const exprList = el[1];
      const l1 = Object.keys(id).length;
      const l2 = Object.keys(exprList).length;

      const result = {};
      if (l1 > 1) {
        if (id.v) {
          const ident = id.v[0] === 'Id' ? id.v[1] : undefined;
          result['ident_decl'] = {
            locinfo: new LocInfo(['loc', id.loc]),
            ident: ident,
          };
        } else {
          // console.warn('TODO: PARSE', id);
          result['unparsed'] = id.map((i) => convertToASTComp(i));
        }
      }
      if (l2 > 0) {
        result['data'] = {
          locinfo: new LocInfo(['loc', exprList.loc]),
          content: convertToASTComp(exprList.v),
        };
      }
      return result;
    });
  }
}

// // eslint-disable-next-line require-jsdoc
// class VernacProof {
//   // TODO: check why this crap is always empty...

//   // eslint-disable-next-line require-jsdoc
//   constructor( array ) {
//     this.rawGenericArg = array[0] || {};
//     this.sectionSubsetExpr = array[1] || {};
//   }
// }

// eslint-disable-next-line require-jsdoc
class CNotation {
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    // TODO not sure what array[1] is
    this.notation = convertToASTComp(array[2]);

    // object of type List<> * List<List> * List<patterns> * List<List<binder>>
    this.constrNotationSubstitution = {
      'exprListOfLists': array[3][1],
      'patternExprs': array[3][2],
      'binderExprsListOfLists': array[3][3],
    };
    this.constrNotationSubstitution['exprList'] = array[3][0].map((el) => ({
      locinfo: new LocInfo(['loc', el.loc]),
      content: convertToASTComp(el.v),
    }));
    // this.notation = array[1];
  }
}

// eslint-disable-next-line require-jsdoc
class CRef {
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    this.libNames = {
      locinfo: new LocInfo(['loc', array[1].loc]),
      content: convertToASTComp(array[1].v),
    };
    if (Object.keys(array[2]).length > 0) {
      console.warn('Still need to parse this...');
    }
    this.instanceExpr = array[2];
  }
}

// eslint-disable-next-line require-jsdoc
class InConstrEntry {
  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    this.data = array[1];
  }
}

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
  'v': GenericVType,
  'VernacRequire': VernacRequire,
  'Ser_Qualid': SerQualid,
  'VernacStartTheoremProof': VernacStartTheoremProof,
  // 'VernacProof': VernacProof, // ported
  'VernacEndProof': VernacEndProof,
  'CNotation': CNotation,
  'InConstrEntry': InConstrEntry,
  'CRef': CRef,
  'CPrim': CPrim,
};

// const currentlyNotParsedTypes = new Set();
const currentlyNotParsedTypes = new Map();

export {
  traverseArray,
  extractCoqAST,
  CoqAST,
  prettyPrint,
  currentlyNotParsedTypes,
};
