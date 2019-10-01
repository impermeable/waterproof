import EditorInterface from '../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from './util/ExpectingSerapiWorker';
import CoqSerapiProcessors
  from '../../../src/coq/serapi/processors/CoqSerapiProcessors';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

const readyResponse = require('./processors/responses/readyResponse');

describe('coq serapi processor interface', () => {
  let serapi;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    serapi = new CoqSerapiProcessors(worker, editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  const sendReady = function() {
    worker.sendMessages(readyResponse);
  };

  it('should not handle setContent when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.contentProcessor, 'setContent', fake);

    serapi.setContent('test content');

    expect(fake.callCount).to.equal(0);
  });

  it('should not handle executeNext when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executeNext', fake);

    serapi.executeNext();

    expect(fake.callCount).to.equal(0);
  });

  it('should not handle executePrevious when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executePrevious', fake);

    serapi.executePrevious();

    expect(fake.callCount).to.equal(0);
  });

  it('should not handle executeTo when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executeTo', fake);

    serapi.executeTo(55);

    expect(fake.callCount).to.equal(0);
  });

  it('should not handle search when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.searchProcessor, 'searchFor', fake);

    serapi.getSearchResults('example query', () => {}, () => {});

    expect(fake.callCount).to.equal(0);
  });

  it('should handle setContent when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.contentProcessor, 'setContent', fake);

    sendReady();

    serapi.setContent('test content');

    expect(fake.callCount).to.equal(1);
  });

  it('should handle executeNext when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executeNext', fake);

    sendReady();

    serapi.executeNext();

    expect(fake.callCount).to.equal(1);
  });

  it('should handle executePrevious when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executePrevious', fake);

    sendReady();

    serapi.executePrevious();

    expect(fake.callCount).to.equal(1);
  });

  it('should handle executeTo when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.executionProcessor, 'executeTo', fake);

    sendReady();

    serapi.executeTo(55);

    expect(fake.callCount).to.equal(1);
  });

  it('should handle search when not ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(serapi.searchProcessor, 'searchFor', fake);

    sendReady();

    serapi.getSearchResults('example query', () => {}, () => {});

    expect(fake.callCount).to.equal(1);
  });

  it('should terminate the worker when stop is called', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(worker, 'terminate', fake);

    sendReady();

    serapi.stop();

    expect(fake.callCount).to.equal(1);
  });

  it('should terminate worker after is ready', () => {
    const fake = sinon.fake.returns(Promise.resolve());
    sinon.replace(worker, 'terminate', fake);

    serapi.stop();

    expect(fake.callCount).to.equal(0);

    sendReady();

    expect(fake.callCount).to.equal(1);
  });
});
