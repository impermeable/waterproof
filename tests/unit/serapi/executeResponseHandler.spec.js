import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';
const parse = require('s-expression');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi execute response handler', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should send a exec message', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    serapi.exec(1);

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Exec');
    expect(serapi.postMessage.lastCall.args[0]).to.include('1');

    done();
  });

  it('should call onSuccess if the execution is successful', (done) => {
    const onSuccess = sinon.fake();
    const onError = sinon.fake();
    const data = {};

    const tag = 'exec-0';
    const ack = 'Ack';
    const complete = 'Completed';

    const send = function(content) {
      serapi.handleExecuteResponse(tag, parse(content),
          onSuccess, onError, data);
    };

    send(ack);
    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(complete);
    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);

    done();
  });

  it('should call onError if the execution fails', (done) => {
    const onSuccess = sinon.fake();
    const onError = sinon.fake();
    const data = {};

    const tag = 'exec-0';
    const ack = 'Ack';
    const errorType = 'CErrors.UserError';
    const error1 = 'last tactic before Qed';
    const error2 = 'Attempt to save an incomplete proof';
    const loc = 4;
    const text1 = `(CoqExn()((3 ${loc}))(Backtrace())` +
        `(${errorType}("${error1}""${error2}")))`;

    const send = function(content) {
      serapi.handleExecuteResponse(tag, parse(content),
          onSuccess, onError, data);
    };

    send(ack);
    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(text1);
    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(1);

    done();
  });

  it('should call onError with the correct message and position', (done) => {
    const onSuccess = sinon.fake();
    const onError = sinon.fake();
    const data = {};

    const tag = 'exec-0';
    const ack = 'Ack';
    const errorType = 'CErrors.UserError';
    const error1 = 'last tactic before Qed';
    const error2 = 'Attempt to save an incomplete proof';
    const loc = 4;
    const lastCorrectSentence = 3;
    const text1 = `(CoqExn()((${lastCorrectSentence} ${loc}))(Backtrace())` +
        `(${errorType}("${error1}""${error2}")))`;

    const send = function(content) {
      serapi.handleExecuteResponse(tag, parse(content),
          onSuccess, onError, data);
    };

    send(ack);
    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(text1);
    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(1);
    const args = onError.lastCall.args[0];
    expect(args.failureAtSentence).to.equal(loc);
    expect(args.lastCorrectSentence).to.equal(lastCorrectSentence);
    expect(args.message).to.equal(error1 + ',' + error2);


    done();
  });
});
