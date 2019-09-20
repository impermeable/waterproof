import ShortKeys from '../../../src/io/shortKey';

const chai = require('chai');
const expect = chai.expect;


const storageLocation = 'shortKeys';
const storage = window.localStorage;
let previousStorage;
describe('Notebook file path', () => {
  before(function() {
    previousStorage = storage.getItem(storageLocation);
    storage.removeItem(storageLocation);
  });

  after(function() {
    storage.setItem(storageLocation, previousStorage);
  });

  it('should use defaults if no storage', (done) => {
    storage.setItem(storageLocation, null);
    const shortKeys = new ShortKeys;
    expect(shortKeys.shortKeys.executeNext).to.be.an('array');
    expect(shortKeys.shortKeys.executeNext).not.to.have.length(0);

    done();
  });

  it('should take a key from storage', (done) => {
    const key = {
      executeNext: ['alt', 'o'],
    };
    storage.setItem(storageLocation, JSON.stringify(key));
    const shortKeys = new ShortKeys;
    expect(shortKeys.shortKeys.executeNext[0]).to.equal(key.executeNext[0]);
    expect(shortKeys.shortKeys.executeNext[1]).to.equal(key.executeNext[1]);

    done();
  });

  it('should reset custom keys after resetShortKeys', (done) => {
    const key = {
      executeNext: ['ctrl', 'o'],
    };
    storage.setItem(storageLocation, JSON.stringify(key));
    const shortKeys = new ShortKeys;
    expect(shortKeys.shortKeys.executeNext[0]).to.equal(key.executeNext[0]);
    expect(shortKeys.shortKeys.executeNext[1]).to.equal(key.executeNext[1]);

    shortKeys.resetShortKeys();

    expect(shortKeys.shortKeys.executeNext[0]).to.not.equal(key.executeNext[0]);
    expect(shortKeys.shortKeys.executeNext[1]).to.not.equal(key.executeNext[1]);

    done();
  });
});
