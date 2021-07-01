/* eslint-disable no-unused-vars */
const chai = require('chai');
const {flattenAST} =
  require('../../../../src/coq/serapi/datastructures/visitor/FlattenVisitor');
const {toAST} = require('./helpers/CoqASTHelpers');
const {empty, emptyAst} = require('./helpers/SExprList');
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const {withLocInfo, coqTypes, woLocInfoKeys} = require('./helpers/classList');

const baseLocation = {
  fname: 'ToplevelInput',
  lineNb: 0,
  lineNbLast: 0,
  bolPos: 0,
  bolPosLast: 0,
  bp: 0,
  ep: 0,
};

describe('AST flattening', () => {
  suppressLogs();

  it('should throw error on empty ast', (done) => {
    const ast = toAST(empty);
    expect(() => flattenAST(ast)).to.throw();
    done();
  });

  describe('types with locinfo should return their location', () => {
    for (const [key, value] of Object.entries(withLocInfo)) {
      it(`${key} should return its location`, (done) => {
        const Constructor = value.class;
        const flatAST = flattenAST(new Constructor(value.data));
        // expect(flattenAST(ast)).to.eql([]);
        let count = 1;
        if (value.count) count = value.count;
        expect(flatAST.length).to.equal(count);
        const [loc, name] = flatAST[0];
        if (!value.skip) {
          expect(name.toLowerCase()).to.equal(key.toLowerCase());
        }
        expect(loc).to.include(baseLocation);
        done();
      });
    }
  });

  describe('types without locinfo should return empty', () => {
    for (const key of woLocInfoKeys) {
      it(`${key} should return no location`, (done) => {
        const value = coqTypes[key];
        const Constructor = value.class;
        const flatAST = flattenAST(new Constructor(value.goodIn));
        expect(flatAST.length).to.equal(0);
        done();
      });
    }
  });
});
