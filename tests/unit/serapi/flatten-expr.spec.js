const parse = require('s-expression');
const {flatten} = require('../../../src/coq/serapi/flatten-expr');

const chai = require('chai');
const expect = chai.expect;

describe('s-expression flattener', () => {
  it('should parse an s-expression correctly', (done) => {
    // Give a sample string, that contains key-value pairs, nested key-value
    // pairs, and entries that are not key-value pairs
    const expression = '(((key1 val1)(key2 ((subkey1 subval1)(subkey2 ' +
        'subval2)))(key3 val3))(not_a_key))';
    const parsed = parse(expression);
    const flattened = flatten(parsed);
    const expected = [
      {
        'key1': 'val1',
        'key2': {
          'subkey1': 'subval1',
          'subkey2': 'subval2',
        },
        'key3': 'val3',
      },
      [
        'not_a_key',
      ],
    ];
    expect(flattened).to.deep.equal(expected);
    done();
  });
});
