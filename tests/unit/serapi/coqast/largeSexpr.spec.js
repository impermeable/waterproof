/* eslint-disable no-unused-vars */
const {toAST} = require('./helpers/CoqASTHelpers');
const {veryLongSexpr, Ltac2NB} = require('./helpers/SExprList');
const chai = require('chai');
// eslint-disable-next-line @typescript-eslint/no-unused-vars
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const {performance} = require('perf_hooks');

const TIME_LIMIT_MS = 40;

describe('Parsing efficiency', () => {
  suppressLogs();

  it(`should parse a long SExpr (${veryLongSexpr.length} chars) quickly`,
      (done) => {
        const start = performance.now();
        const ast = toAST(veryLongSexpr);
        const end = performance.now();

        expect(end - start).to.be.at.most(TIME_LIMIT_MS);
        done();
      });

  it(`should parse many SExprs quickly (${Ltac2NB.length} chars)`, (done) => {
    const start = performance.now();
    Ltac2NB.split('\n').forEach((sentence) => {
      const ast = toAST(sentence);
      expect(ast.constructor.name).to.equal('CoqAST');
    });
    const end = performance.now();
    expect(end - start).to.be.at.most(TIME_LIMIT_MS);
    done();
  });
});
