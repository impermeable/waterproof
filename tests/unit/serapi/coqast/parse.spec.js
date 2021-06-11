/* eslint-disable no-unused-vars */
const {toAST, astHasChild} = require('./CoqASTHelpers');

const chai = require('chai');
const {emptyAst, empty, sexp1} = require('./helpers/SExprList');
// eslint-disable-next-line @typescript-eslint/no-unused-vars
const expect = chai.expect;

it.skip('should parse an empty Coq AST s-expr correctly', (done) => {
  const ast = toAST(emptyAst);

  expect(ast.constructor.name).to.equal('CoqAST');
  expect(ast.content).to.eql([]);
  expect(ast.locinfo.line_nb).to.equal(1);

  done();
});

it.skip('shoud produce empty AST for empty S-Expr', (done) => {
  const ast = toAST(empty);
  expect(ast).to.equal(null);
  done();
});

it('should parse simple S-Expr', (done) => {
  const ast = toAST(sexp1, true);
  // expect(ast.constructor.name).to.equal('CoqAST');
  astHasChild(ast, '');
  done();
});
