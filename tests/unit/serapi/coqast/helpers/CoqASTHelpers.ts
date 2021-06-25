import {CoqAST, extractCoqAST} from
  '../../../../../src/coq/serapi/ASTProcessor';
import CoqType from '../../../../../src/coq/serapi/datastructures/CoqType';
const parse = require('s-expression');
const {performance} = require('perf_hooks');
// const flatten = require('../../../../src/coq/serapi/flatten-expr').flatten;

/**
 * Convert an S-expression to an AST data-structure
 * @param {string} sExpr The input CoqAST
 * @param {boolean} logging if the output should be logged.
 * @return {CoqAST} the ast of the expression
 */
function toAST(sExpr: string, logging=false): CoqAST {
  const arrayData = parse(sExpr);
  if (logging) {
    console.log('toAST - array data:', arrayData);
  }
  const ast = extractCoqAST(arrayData);
  if (logging) {
    console.warn('toAST - CoqAst', ast);
  }
  return ast;
}

function toASTWithTime(sExpr: string, logging=false): [CoqAST, number] {
  const start = performance.now();
  const ast = toAST(sExpr);
  const end = performance.now();
  return [ast, end-start];
}

/**
 * Given a coqtype, check if a child exists in the
 * child hierarchy.
 * @param {CoqType} ast
 * @param {string} target
 * @return {boolean}
 */
function astHasChild(ast: CoqType, target: string) : boolean {
  const pathSet : Set<string>= new Set(keyify(ast));
  return [...pathSet].some((path) => path.includes(target));
}

const keyify = (obj, prefix = '') : string[] =>
  Object.keys(obj).reduce((res, el) : any => {
    if ( Array.isArray(obj[el]) ) {
      return [...res, ...keyify(obj[el], prefix)];
    } else if ( typeof obj[el] === 'object' && obj[el] !== null ) {
      // console.log('res', res, obj);
      const e = ['Object', 'String'].includes(obj[el].constructor.name) ?
          '' : obj[el].constructor.name+'.';
      return [...res, ...keyify(obj[el], prefix + e)];
    }
    return [...res, prefix];
  }, []);

export {
  toAST,
  toASTWithTime,
  astHasChild,
  keyify,
  objHasKeys,
  BAD_CONST_INPUTS,
};

const BAD_CONST_INPUTS = [
  {}, ' ', null, undefined, 42,
];

function objHasKeys(obj, ...args) {
  return args.every((key) =>
    Object.prototype.hasOwnProperty.call(obj, key),
  );
}
