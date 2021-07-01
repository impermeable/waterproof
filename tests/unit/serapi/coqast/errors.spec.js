/* eslint-disable no-unused-vars */
const chai = require('chai');
const expect = chai.expect;
const suppressLogs = require('mocha-suppress-logs');
const {coqTypes} = require('./helpers/classList');
const {BAD_CONST_INPUTS} = require('./helpers/CoqASTHelpers');


describe('Error checking for CoqAST objects', () => {
  suppressLogs();

  for (const [key, value] of Object.entries(coqTypes)) {
    // console.log(`${key}: ${value}`);
    describe(`Tests for the type ${key}:`, () => {
      it('should throw an error on wrong input types', (done) => {
        // console.log(value);
        const ConstructorForObject = value.class;
        BAD_CONST_INPUTS.forEach((e) => {
          expect(() => new ConstructorForObject(e)).to
              .throw(TypeError);
        });
        done();
      });

      it('should create a class on good input', (done) => {
        const ConstructorForObject = value.class;
        const array = value.goodIn;
        try {
          const astObj = new ConstructorForObject(array);
        } catch (e) {
          // console.log(e);
          expect.fail('something went wrong: ' + e);
        }
        done();
      });
    });
  }
});
