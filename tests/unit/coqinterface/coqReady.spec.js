import CoqSerapi from '../../../src/coq/serapi/CoqSerapi';
import SerapiInterface from '../../../src/coq/serapi/SerapiInterface';
import EditorInterface from '../../../src/coq/EditorInterface';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('coq ready signals', () => {
  const serapi = new SerapiInterface;
  const callbacks = new EditorInterface;

  let impl;

  // Before each test, reset the call counts etc. of all the fake functions
  beforeEach(() => {
    serapi.isReady = () => false;
    sandbox.replace(serapi, 'add', sinon.fake());
    sandbox.replace(serapi, 'cancel', sinon.fake());
    sandbox.replace(serapi, 'exec', sinon.fake());
    sandbox.replace(serapi, 'goals', sinon.fake());
    sandbox.replace(serapi, 'search', sinon.fake());
    serapi.query = sinon.fake();
    sandbox.replace(serapi, 'terminate', sinon.fake());
    impl = new CoqSerapi(serapi, callbacks);
  });

  afterEach(() => {
    sandbox.restore();
  });

  const checkNoSerapiCalls = () => {
    expect(serapi.add.callCount).to.equal(0);
    expect(serapi.cancel.callCount).to.equal(0);
    expect(serapi.exec.callCount).to.equal(0);
    expect(serapi.goals.callCount).to.equal(0);
    expect(serapi.search.callCount).to.equal(0);
    expect(serapi.query.callCount).to.equal(0);
  };

  it('should not call any serapi methods if not ready for \'setContent\'',
      (done) => {
        impl.setContent('Lemma a n:n+0=n.');
        checkNoSerapiCalls();
        done();
      });

  it('should not call any serapi methods if not ready for \'getSearchResults\'',
      (done) => {
        impl.getSearchResults('plus', () => {}, () => {});
        checkNoSerapiCalls();
        done();
      });

  it('should not call any serapi methods if not ready for \'query\'',
      (done) => {
        impl.query('plus', () => {}, () => {});
        checkNoSerapiCalls();
        done();
      });

  it('should call terminate when stopping coqserapi', (done) => {
    expect(serapi.terminate.callCount).to.equal(0);
    impl.stop();
    expect(serapi.terminate.callCount).to.equal(1);
    done();
  });
});
