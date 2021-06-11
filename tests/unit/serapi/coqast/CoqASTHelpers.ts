import {CoqAST, extractCoqAST} from '../../../../src/coq/serapi/ASTProcessor';
import CoqType from '../../../../src/coq/serapi/datastructures/CoqType';
const parse = require('s-expression');
// const flatten = require('../../../../src/coq/serapi/flatten-expr').flatten;

/**
 * Convert an S-expression to an AST data-structure
 * @param {string} sExpr The input CoqAST
 * @param {boolean} logging if the output should be logged.
 * @return {CoqAST} the ast of the expression
 */
function toAST(sExpr: string, logging=false): CoqAST {
  const arrayData = parse(sExpr);
  console.warn(sExpr);
  // if (logging) {
  //   console.log('array data:', arrayData);
  // }
  const ast = extractCoqAST(arrayData);
  if (logging) {
    console.warn('CoqAst', ast);
  }
  return ast;
}

function astHasChild(ast: CoqType, target: string) {
  console.log(keyify(ast));
  // const parts = propStr.split('.');
  // const cur = ast;
  // for (var i=0; i<parts.length; i++) {
  //     if (!cur[parts[i]])
  //         return false;
  //     cur = cur[parts[i]];
  // }
  // return true;
}

const keyify = (obj, prefix = '') =>
  Object.keys(obj).reduce((res, el) : any => {
    if ( Array.isArray(obj[el]) ) {
      return res;
    } else if ( typeof obj[el] === 'object' && obj[el] !== null ) {
      console.log('res', res, obj);
      return [...res, ...keyify(obj[el], prefix + el + '.')];
    }
    return [...res, prefix + el];
  }, []);

export {
  toAST,
  astHasChild,
};
