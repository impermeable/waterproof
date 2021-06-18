/* eslint-disable no-unused-vars */
const chai = require('chai');
const {flattenAST} =
  require('../../../../src/coq/serapi/datastructures/visitor/FlattenVisitor');
const {toAST} = require('./helpers/CoqASTHelpers');
const {empty, emptyAst} = require('./helpers/SExprList');
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const {withLocInfo, coqTypes} = require('./helpers/classList');

const baseLocation = {
  fname: 'ToplevelInput',
  line_nb: 0,
  line_nb_last: 0,
  bol_pos: 0,
  bol_pos_last: 0,
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
        expect(flattenAST.length).to.equal(1);
        const [loc, name] = flatAST[0];
        expect(name.toLowerCase()).to.equal(key.toLowerCase());
        expect(loc).to.include(baseLocation);
        done();
      });
    }
  });
});
