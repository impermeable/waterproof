import SerapiWorkerTCP
  from '../../../../src/coq/serapi/workers/SerapiWorkerTCP';

const sinon = require('sinon');
const chai = require('chai');
const expect = chai.expect;


describe('TCP Worker for serapi', () => {
  afterEach(() => {
    sinon.restore();
  });

  const createWorkerWithId = (id=0) => {
    let called = false;
    const socket = {
      sendMessage: () => {
        called = true;
      },
    };
    const worker = new SerapiWorkerTCP(socket);
    // only set it here so that the initial message is not counted
    if (!called) {
      throw new Error('Worker does call create message at start');
    }
    worker.socketId = id;
    socket.sendMessage = sinon.fake();
    worker.onMessage = sinon.fake();
    return worker;
  };

  it('should start by sending a create message', (done) => {
    const fakeSocket = {};
    fakeSocket.sendMessage = sinon.fake();
    new SerapiWorkerTCP(fakeSocket);
    expect(fakeSocket.sendMessage.callCount).to.equal(1);
    const lastMessage = fakeSocket.sendMessage.lastArg;
    expect(lastMessage).to.be.a('string');
    try {
      const json = JSON.parse(lastMessage);
      expect(json).to.include({
        verb: 'create',
      });
    } catch (e) {
      done(e);
    }
    done();
  });

  it('should warn if a message is send before it has a socket id', (done) => {
    const fakeSocket = {};
    fakeSocket.sendMessage = sinon.fake();
    sinon.replace(console, 'warn', sinon.fake());
    const worker = new SerapiWorkerTCP(fakeSocket);
    expect(console.warn.callCount).to.equal(0);
    worker.postMessage('Test message');
    expect(console.warn.callCount).to.equal(1);
    done();
  });

  it('should send the correct message when forwarding', (done) => {
    const worker = createWorkerWithId();
    const message = '(add-1 (Add () "Lemm")';

    worker.postMessage(message);

    expect(worker.socket.sendMessage.callCount).to.equal(1);
    const lastMessage = worker.socket.sendMessage.lastArg;
    expect(lastMessage).to.be.a('string');
    try {
      const json = JSON.parse(lastMessage);
      expect(json).to.include({
        verb: 'forward',
        instance_id: 0,
        content: message,
      });
    } catch (e) {
      done(e);
    }
    done();
  });

  it('should send the correct message when terminating', (done) => {
    const worker = createWorkerWithId();

    worker.terminate();

    expect(worker.socket.sendMessage.callCount).to.equal(1);
    const lastMessage = worker.socket.sendMessage.lastArg;
    expect(lastMessage).to.be.a('string');
    try {
      const json = JSON.parse(lastMessage);
      expect(json).to.include({
        verb: 'destroy',
        instance_id: 0,
      });
    } catch (e) {
      done(e);
    }
    done();
  });

  it('should forward received messages', (done) => {
    const worker = createWorkerWithId();
    const message = 'Receiving message';
    worker.handleMessage(message);

    expect(worker.onMessage.callCount).to.equal(1);

    const lastMessage = worker.onMessage.lastArg;
    expect(lastMessage).to.be.a('string').to.equal(message);
    done();
  });

  it('should ignore empty messages', (done) => {
    const worker = createWorkerWithId();
    const message = '';
    worker.handleMessage(message);

    expect(worker.onMessage.callCount).to.equal(0);

    done();
  });
});
