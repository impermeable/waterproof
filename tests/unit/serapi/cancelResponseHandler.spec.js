import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';
const parse = require('s-expression');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi cancel response handler', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should send a cancel message for a single id', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    serapi.cancel(1);

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Cancel');
    expect(serapi.postMessage.lastCall.args[0]).to.include('(1)');

    done();
  });

  it('should send a cancel message for a multiple ids', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const ids = [1, 2, 3];
    serapi.cancel(ids);
    const list = '(' + ids.join(' ') + ')';

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Cancel');
    expect(serapi.postMessage.lastCall.args[0]).to.include(list);

    done();
  });

  it('should call onSuccess on a valid response', (done) => {
    const data = {};
    const tag = 'cancel-0';
    const ack = 'Ack';
    const text1 = '(Cancelled(3))';
    const complete = 'Completed';
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    const send = function(content) {
      serapi.handleCancelResponse(tag, parse(content),
          onSuccess, onError, data);
    };

    send(ack);
    send(text1);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    expect(data.exceptionOccurred).to.be.equal(false);
    send(complete);

    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);
    expect(data.exceptionOccurred).to.be.equal(false);

    done();
  });

  it('should return the correct list of cancelled sentences', (done) => {
    const data = {};
    const tag = 'cancel-0';
    const ack = 'Ack';
    const text1 = '(Canceled(3 4 56))';
    const complete = 'Completed';
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    const send = function(content) {
      serapi.handleCancelResponse(tag, parse(content),
          onSuccess, onError, data);
    };

    send(ack);
    send(text1);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    expect(data.exceptionOccurred).to.be.equal(false);
    send(complete);

    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);
    expect(data.exceptionOccurred).to.be.equal(false);

    expect(data.removedSentences).to.be.eql([3, 4, 56]);
    done();
  });
});
