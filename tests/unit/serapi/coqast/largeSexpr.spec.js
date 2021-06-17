/* eslint-disable no-unused-vars */
const {toAST} = require('./helpers/CoqASTHelpers');
const {veryLongSexpr} = require('./helpers/SExprList');
const chai = require('chai');
// eslint-disable-next-line @typescript-eslint/no-unused-vars
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const {performance} = require('perf_hooks');

describe('Parsing CoqASTs', () => {
  suppressLogs();

  it(`should parse an ast fast (${veryLongSexpr.length} chars)`, (done) => {
    const start = performance.now();
    const ast = toAST(veryLongSexpr);
    const end = performance.now();

    expect(end - start).to.be.at.most(40);
    done();
  });
});
