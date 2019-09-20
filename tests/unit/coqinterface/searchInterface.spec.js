import CoqSerapi from '../../../src/coq/serapi/CoqSerapi';
import SerapiInterface from '../../../src/coq/serapi/SerapiInterface';
import EditorInterface from '../../../src/coq/EditorInterface';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('getSearchResults', () => {
  // Replace all the functions of the interface with SerAPI by fakes
  // See https://sinonjs.org/releases/v7.3.2/fakes/
  const serapi = new SerapiInterface;
  const callbacks = new EditorInterface;

  let impl;
  let searchSpy;

  // Before each test, reset the call counts etc. of all the fake functions
  beforeEach(() => {
    searchSpy = sinon.spy(serapi, 'search');
    impl = new CoqSerapi(serapi, callbacks);
  });

  afterEach(() => {
    sinon.restore();
    sandbox.restore();
  });

  it('should call the "search" method if the button is clicked', (done) => {
    const searchQuery = '_ + _';
    impl.getSearchResults(searchQuery, () => {}, () => {});
    expect(searchSpy.callCount).to.be.equal(1);
    expect(searchSpy.lastCall.args[0]).to.be.equal(searchQuery);
    done();
  });
});
