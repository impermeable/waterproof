import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';
const parse = require('s-expression');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi goals response handler', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should send a goals message', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    serapi.goals(1);

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Goals');
    expect(serapi.postMessage.lastCall.args[0]).to.include('1');
    expect(serapi.postMessage.lastCall.args[0]).to.include('PpStr');

    done();
  });

  it('should call onSuccess if the response indicates success', (done) => {
    const ack = 'Ack';
    const goal = 'forall n: nat, n + 0 = n';
    const text1 = `(ObjList((CoqString"${goal}")))`;
    const complete = 'Completed';

    const tag = 'Ack';
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    const data = {};

    const send = function(content) {
      serapi.handleGoalsResponse(tag, parse(content), onSuccess, onError, data);
    };

    send(ack);
    send(text1);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(complete);

    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);

    expect(data.completed).to.be.equal(true);
    expect(data.goal).to.be.equal(goal);

    done();
  });
});
