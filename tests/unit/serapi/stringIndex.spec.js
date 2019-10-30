import {byteIndexToStringIndex} from '../../../src/coq/serapi/SerapiParser';

const chai = require('chai');
const expect = chai.expect;

describe('serapi index calculator', () => {
  it('should give 0 for 0 with empty string', (done) => {
    const string = '';
    const result = byteIndexToStringIndex(string, 0);
    expect(result).to.equal(0);
    done();
  });

  it('should give 0 for 0 on a non empty string', (done) => {
    const string = 'Not an empty string';
    const result = byteIndexToStringIndex(string, 0);
    expect(result).to.equal(0);
    done();
  });

  it('should give 0 for 0 on a string with utf8 chars', (done) => {
    const string = 'αℚ∀🤔🅱';
    const result = byteIndexToStringIndex(string, 0);
    expect(result).to.equal(0);
    done();
  });

  it('should give ? for out of bounds index', (done) => {
    const string = '';
    const result = byteIndexToStringIndex(string, 1);
    expect(result).to.equal(-1);
    done();
  });

  it('should give the correct index for ascii chars', (done) => {
    const string = 'Not an empty string';
    for (let i = 0; i < string.length; i++) {
      const result = byteIndexToStringIndex(string, i);
      expect(result).to.equal(i);
    }
    done();
  });

  it('should give the correct index for utf8 chars', (done) => {
    const string = 'αεℚ∀🤔🅱';
    let result = byteIndexToStringIndex(string, 2);
    expect(result).to.equal(1);
    result = byteIndexToStringIndex(string, 4);
    expect(result).to.equal(2);
    done();
  });
});
