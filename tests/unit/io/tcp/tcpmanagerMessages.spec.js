import TCPManager from '../../../../src/coq/serapi/workers/TCPManager';

const sinon = require('sinon');
const chai = require('chai');
const expect = chai.expect;


describe('TCP manager', () => {
  beforeEach(() => {
    sinon.replace(console, 'log', sinon.fake());
    sinon.replace(console, 'warn', sinon.fake());
  });

  afterEach(() => {
    sinon.restore();
  });

  const addWorker = (manager, id) => {
    const worker = manager.createNewWorker();
    worker.socketId = id;
    return worker;
  };

  it('should be able to create a serapi tcp worker', (done) => {
    const manager = new TCPManager(51613, false);

    sinon.replace(manager, 'sendMessage', sinon.fake());

    const worker = manager.createNewWorker();

    expect(worker.socketId).to.equal(-1);
    expect(worker.socket).to.equal(manager);
    expect(manager.sendMessage.callCount).to.equal(1);

    done();
  });

  it('should assign an id to a worker with none', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    const worker = manager.createNewWorker();

    expect(worker.socketId).to.equal(-1);

    const idMessage = {
      verb: 'create',
      status: 'success',
      instance_id: 0,
      content: '',
    };

    manager.handleMessage(JSON.stringify(idMessage));

    expect(worker.socketId).to.equal(0);

    expect(manager.socketById(0)).to.be.at.least(0);
    expect(manager.socketById(-1)).to.equal(-1);

    done();
  });

  it('should not assign an id to all workers with none', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    const worker1 = manager.createNewWorker();
    const worker2 = manager.createNewWorker();

    expect(worker1.socketId).to.equal(-1);
    expect(worker2.socketId).to.equal(-1);

    const idMessage = {
      verb: 'create',
      status: 'success',
      instance_id: 0,
      content: '',
    };

    manager.handleMessage(JSON.stringify(idMessage));

    expect(worker1.socketId).to.equal(0);
    expect(worker2.socketId).to.equal(-1);

    idMessage.instance_id = 1;

    manager.handleMessage(JSON.stringify(idMessage));

    expect(worker1.socketId).to.equal(0);
    expect(worker2.socketId).to.equal(1);

    done();
  });

  it('should forward messages to the appropriate worker', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    const worker1 = addWorker(manager, 0);
    const worker2 = addWorker(manager, 1);

    sinon.replace(worker1, 'handleMessage', sinon.fake());
    sinon.replace(worker2, 'handleMessage', sinon.fake());

    const forwardMessage = {
      verb: 'forward',
      status: 'success',
      instance_id: 0,
      content: 'Text content',
    };

    manager.handleMessage(JSON.stringify(forwardMessage));

    expect(worker1.handleMessage.callCount).to.equal(1);
    expect(worker2.handleMessage.callCount).to.equal(0);

    forwardMessage.instance_id = 1;
    manager.handleMessage(JSON.stringify(forwardMessage));

    expect(worker1.handleMessage.callCount).to.equal(1);
    expect(worker2.handleMessage.callCount).to.equal(1);

    done();
  });

  it('should ignore failed messages', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    const worker1 = addWorker(manager, 0);

    sinon.replace(worker1, 'handleMessage', sinon.fake());

    const forwardMessage = {
      verb: 'forward',
      status: 'failure',
      instance_id: 0,
      content: 'Text content',
    };

    manager.handleMessage(JSON.stringify(forwardMessage));

    done();
  });

  it('should destroy worker when destroy message is received', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    addWorker(manager, 0);
    addWorker(manager, 1);

    const destroyMessage = {
      verb: 'destroy',
      status: 'success',
      instance_id: 0,
      content: '',
    };

    expect(manager.socketById(0)).to.not.equal(-1);
    expect(manager.socketById(1)).to.not.equal(-1);

    manager.handleMessage(JSON.stringify(destroyMessage));

    expect(manager.socketById(0)).to.equal(-1);
    expect(manager.socketById(1)).to.not.equal(-1);

    done();
  });

  it('should call the destructor callback when all workers are destroyed',
      (done) => {
        const manager = new TCPManager(51613, false);
        sinon.replace(manager, 'sendMessage', sinon.fake());
        addWorker(manager, 0);

        const destroyMessage = {
          verb: 'destroy',
          status: 'success',
          instance_id: 0,
          content: '',
        };

        const disconnectFake = sinon.fake();
        manager.disconnecting = disconnectFake;

        manager.handleMessage(JSON.stringify(destroyMessage));
        expect(disconnectFake.callCount).to.equal(1);
        expect(manager.disconnecting).to.equal(null);


        done();
      });

  it('should terminate all workers when stopAll is called', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    addWorker(manager, 0);
    addWorker(manager, 1);

    const currentCalls = manager.sendMessage.callCount;

    manager.stopAll(null);

    expect(manager.sendMessage.callCount).to.equal(currentCalls + 2);
    done();
  });

  it('should not shutdown twice all workers when stopAll is called', (done) => {
    const manager = new TCPManager(51613, false);
    sinon.replace(manager, 'sendMessage', sinon.fake());

    addWorker(manager, 0);
    addWorker(manager, 1);

    const currentCalls = manager.sendMessage.callCount;

    manager.stopAll(() => {});

    expect(manager.sendMessage.callCount).to.equal(currentCalls + 2);

    manager.stopAll(() => {});
    expect(manager.sendMessage.callCount).to.equal(currentCalls + 2);

    done();
  });
});
