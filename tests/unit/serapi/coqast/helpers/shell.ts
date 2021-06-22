const repl = require('repl');

const ds = require('../../../../../src/coq/serapi/datastructures/index.ts');
import {toAST} from './CoqASTHelpers';
import {emptyAst, sexp1} from './SExprList';

function addToContext(repl, k, v, options) {
  Object.defineProperty(repl.context, k, {
    configurable: options.configurable ?? false,
    enumerable: options.enumerable ?? true,
    value: v,
  });
}

const msg = 'message';
console.log('Node REPL');

const r = repl.start({prompt: '\u001b[35mλ\u001b[0m ', useColors: true});

addToContext(r, 'm', msg, {});
addToContext(r, 'toAST', toAST, {});
addToContext(r, 'goodSExp', sexp1, {});
addToContext(r, 'badSExp', emptyAst, {});

// console.log(`Loaded datastrcutures: ${Object.keys(ds.default).length}`);
Object.keys(ds.default).forEach((prop) => {
  addToContext(r, prop, ds.default[prop], {});
});
