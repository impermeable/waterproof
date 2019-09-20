import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';

const parse = require('s-expression');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi add response handler', () => {
  let serapi;

  beforeEach(() => {
    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should call onSuccess if no error occurred', (done) => {
    const data = {};
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    const idx1 = 0; const idx2 = 34;
    // const idx3 = 35; const idx4 = 41;
    const sid1 = 2;
    // const sid2 = 3;

    const tag = 'add-0';
    const ack = 'Ack';
    const text1 = `(Added ${sid1}((fname ToplevelInput)(line_nb 1)(bol_pos 0)`
        + `(line_nb_last 1)(bol_pos_last 0)(bp ${idx1})(ep ${idx2}))NewTip)`;
    const complete = 'Completed';

    const send = function(content) {
      serapi.handleAddResponse(tag, parse(content), onSuccess, onError, data);
    };

    // Give the Ack and Added responses
    // onSuccess and onError should not be called yet
    send(ack);
    send(text1);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    // Now, send the Complete and then we should get results
    send(complete);
    expect(data.exceptionOccurred).to.be.equal(false);
    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);

    done();
  });

  it('should call onError if an error occurred', (done) => {
    const idx1 = 12;
    const idx2 = 63;
    const type = 'Stream.Error';
    const description = 'illegal begin of vernac';
    const ack = 'Ack';
    const msg = `(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
        `(line_nb_last 1)(bol_pos_last 0)(bp ${idx1})(ep ${idx2})))` +
        `()(Backtrace())(${type}"${description}"))`;
    const complete = 'Completed';

    const tag = 'add-0';
    const onSuccess = sinon.fake();
    const onError = sinon.fake();
    const data = {};

    const send = function(content) {
      serapi.handleAddResponse(tag, parse(content), onSuccess, onError, data);
    };

    send(ack);
    send(msg);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(complete);
    expect(data.exceptionOccurred).to.be.equal(true);

    expect(onSuccess.callCount).to.be.equal(1);
    expect(onSuccess.lastCall.args[0].length).to.be.equal(0);
    expect(onError.callCount).to.be.equal(1);

    const expectedException = {
      beginIndex: idx1,
      endIndex: idx2,
      message: description,
    };

    expect(data.exception).to.include(expectedException);

    done();
  });

  it('should report results with the correct sentence data', (done) => {
    const data = {};
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    const idx1 = 0; const idx2 = 34; const idx3 = 35; const idx4 = 41;
    const sid1 = 2; const sid2 = 3;

    const tag = 'add-0';
    const ack = 'Ack';
    const text1 = `(Added ${sid1}((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
        `(line_nb_last 1)(bol_pos_last 0)(bp ${idx1})(ep ${idx2}))NewTip)`;
    const text2 = `(Added ${sid2}((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
        `(line_nb_last 1)(bol_pos_last 0)(bp ${idx3})(ep ${idx4}))NewTip)`;
    const complete = 'Completed';

    const send = function(content) {
      serapi.handleAddResponse(tag, parse(content), onSuccess, onError, data);
    };

    // Give the Ack and Added responses
    // onSuccess and onError should not be called yet
    send(ack);
    send(text1);
    send(text2);

    expect(onSuccess.callCount).to.be.equal(0);
    expect(onError.callCount).to.be.equal(0);

    send(complete);

    expect(data.exceptionOccurred).to.be.equal(false);
    expect(onSuccess.callCount).to.be.equal(1);
    expect(onError.callCount).to.be.equal(0);
    const expectedResponse = [
      {sentenceId: sid1, beginIndex: idx1, endIndex: idx2, sentence: ''},
      {sentenceId: sid2, beginIndex: idx3, endIndex: idx4, sentence: ''},
    ];
    const response = onSuccess.lastCall.args[0];
    expect(response).to.be.eql(expectedResponse);

    done();
  });

  it('should correctly escape double quotes', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const code = '(*"This """is" text"*)';
    const expectedCommand = String.raw`(Add () "(*\"This \"\"\"is\" text\"*)")`;
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    serapi.add(code, onSuccess, onError);
    expect(serapi.postMessage.callCount).to.be.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.be.equal(expectedCommand);
    done();
  });

  it('should correctly escape slashes', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const code = String.raw`(*\\This \is\ text\'*)`;
    const expectedCommand = String.raw`(Add () "(*\\\\This \\is\\ text\\'*)")`;
    const onSuccess = sinon.fake();
    const onError = sinon.fake();

    serapi.add(code, onSuccess, onError);
    expect(serapi.postMessage.callCount).to.be.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.be.equal(expectedCommand);
    done();
  });
});
