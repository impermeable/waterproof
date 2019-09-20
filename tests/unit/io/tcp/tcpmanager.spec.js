import TCPManager from '../../../../src/coq/serapi/workers/TCPManager';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;


describe('TCP manager input buffering', () => {
  let manager;

  beforeEach(() => {
    manager = new TCPManager(7001, false);

    sandbox.replace(manager, 'handleMessage', sinon.fake());
  });
  afterEach(() => {
    sandbox.restore();
  });

  const createNumber = (num) => {
    const buffer = Buffer.alloc(4);
    buffer.writeInt32BE(num);
    return buffer;
  };

  const createString = (string) => {
    return Buffer.from(string, 'utf8');
  };

  const createStringWithNumb = (string) => {
    const messageBuffer = createString(string);
    const numberBuffer = createNumber(messageBuffer.length);
    return Buffer.concat([numberBuffer, messageBuffer]);
  };

  it('should handle a full message in a single buffer', (done) => {
    const message = 'Test message';
    manager.handleBuffer(createStringWithNumb(message));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle a zero size message', (done) => {
    const message = '';
    manager.handleBuffer(createStringWithNumb(message));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle two messages in one buffer', (done) => {
    const message1 = 'First message';
    const message2 = 'Second message';
    const buffer = Buffer.concat([
      createStringWithNumb(message1),
      createStringWithNumb(message2),
    ]);
    manager.handleBuffer(buffer);

    expect(manager.handleMessage.callCount).to.be.equal(2);
    expect(manager.handleMessage.getCall(0).lastArg).to.equal(message1);
    expect(manager.handleMessage.getCall(1).lastArg).to.equal(message2);

    done();
  });

  it('should handle a messages too long for the first buffer', (done) => {
    const message = 'First message';
    const buffer = createStringWithNumb(message);
    manager.handleBuffer(buffer.slice(0, 8));
    manager.handleBuffer(buffer.slice(8));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle a message spread over three buffers', (done) => {
    const message = 'First message';
    const buffer = createStringWithNumb(message);
    manager.handleBuffer(buffer.slice(0, 7));
    manager.handleBuffer(buffer.slice(7, 10));
    manager.handleBuffer(buffer.slice(10));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle the size bits being split over buffers', (done) => {
    const message = 'First message';
    const buffer = createStringWithNumb(message);
    manager.handleBuffer(buffer.slice(0, 1));
    manager.handleBuffer(buffer.slice(1, 2));
    manager.handleBuffer(buffer.slice(2, 3));
    manager.handleBuffer(buffer.slice(3, 4));
    manager.handleBuffer(buffer.slice(4));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle the size bits being split over buffers', (done) => {
    const message1 = 'First message';
    const message2 = 'Second message';
    const buffer = createStringWithNumb(message1);
    const buffer2 = createStringWithNumb(message2);
    manager.handleBuffer(buffer.slice(0, 1));
    manager.handleBuffer(buffer.slice(1, 2));
    manager.handleBuffer(buffer.slice(2, 3));
    manager.handleBuffer(buffer.slice(3, 4));
    manager.handleBuffer(Buffer.concat([
      buffer.slice(4),
      buffer2.slice(0, 4),
    ]));
    expect(manager.handleMessage.callCount).to.be.equal(1);
    manager.handleBuffer(buffer2.slice(4));

    expect(manager.handleMessage.callCount).to.be.equal(2);
    expect(manager.handleMessage.getCall(0).lastArg).to.equal(message1);
    expect(manager.handleMessage.getCall(1).lastArg).to.equal(message2);

    done();
  });

  it('should handle a message split into single bytes', (done) => {
    const message = 'First message';
    const buffer = createStringWithNumb(message);
    for (let i = 0; i < buffer.length; i++) {
      expect(manager.handleMessage.callCount).to.be.equal(0);
      manager.handleBuffer(buffer.slice(i, i + 1));
    }

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.equal(message);

    done();
  });

  it('should handle a message split into single bytes with utf-8 characters',
      (done) => {
        const message = 'First message';
        const buffer = createStringWithNumb(message);
        for (let i = 0; i < buffer.length; i++) {
          expect(manager.handleMessage.callCount).to.be.equal(0);
          manager.handleBuffer(buffer.slice(i, i + 1));
        }

        expect(manager.handleMessage.callCount).to.be.equal(1);
        expect(manager.handleMessage.lastArg).to.equal(message);

        done();
      });

  it('should handle a half a message and then a full one in two buffers',
      (done) => {
        const message1 = 'First message';
        const message2 = 'Second message';
        const buffer1 = createStringWithNumb(message1);
        manager.handleBuffer(buffer1.slice(0, 8));
        manager.handleBuffer(Buffer.concat([
          buffer1.slice(8),
          createStringWithNumb(message2),
        ]));

        expect(manager.handleMessage.callCount).to.be.equal(2);

        expect(manager.handleMessage.getCall(0).lastArg).to.equal(message1);
        expect(manager.handleMessage.getCall(1).lastArg).to.equal(message2);

        done();
      });


  it('should handle utf-8 character', (done) => {
    const message = 'αℚ∀🤔🅱';
    manager.handleBuffer(createStringWithNumb(message));

    expect(manager.handleMessage.callCount).to.be.equal(1);
    expect(manager.handleMessage.lastArg).to.be.equal(message);

    done();
  });

  it('should handle messages spliced at any point', (done) => {
    const testMessage1 = '🅱️li🅱e 🤔';
    const testMessage2 = 'Cα🐛';
    const testBuffer = Buffer.concat([
      createStringWithNumb(testMessage1),
      createStringWithNumb(testMessage2),
    ]);


    for (let i = 1; i < testBuffer.length; i++) {
      for (let j = i; j < testBuffer.length; j++) {
        manager.handleBuffer(testBuffer.slice(0, i));
        manager.handleBuffer(testBuffer.slice(i, j));
        manager.handleBuffer(testBuffer.slice(j));

        expect(manager.handleMessage.callCount).to.be.equal(2);

        expect(manager.handleMessage.getCall(0).lastArg).to.equal(testMessage1);
        expect(manager.handleMessage.getCall(1).lastArg).to.equal(testMessage2);

        sandbox.restore();
        sandbox.replace(manager, 'handleMessage', sinon.fake());
      }
    }
    done();
  });
});
