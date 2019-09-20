import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';
const parse = require('s-expression');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi search response handler', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should call onSuccess only after all three commands have been executed',
      (done) => {
        const onSuccess = sinon.fake();

        const tag = 'search-0';
        const ack = 'Ack';
        const complete = 'Completed';

        const send = function(content) {
          serapi.handleSearchResponse(tag, parse(content),
              onSuccess);
        };

        send(ack);
        expect(onSuccess.callCount).to.be.equal(0);

        send(complete);
        expect(onSuccess.callCount).to.be.equal(0);
        send(complete);
        expect(onSuccess.callCount).to.be.equal(0);
        send(complete);
        expect(onSuccess.callCount).to.be.equal(1);

        done();
      });

  it('should ignore results from other searches', (done) => {
    const onSuccess = sinon.fake();

    let tag = 'search-0';
    const ack = 'Ack';
    const complete = 'Completed';

    const send = function(content) {
      serapi.handleSearchResponse(tag, parse(content),
          onSuccess);
    };

    send(ack);
    expect(onSuccess.callCount).to.be.equal(0);

    send(complete);
    expect(onSuccess.callCount).to.be.equal(0);
    send(complete);
    expect(onSuccess.callCount).to.be.equal(0);

    tag = 'search-1';
    send(complete);

    expect(onSuccess.callCount).to.be.equal(0);

    tag = 'search-0';
    send(complete);

    expect(onSuccess.callCount).to.be.equal(1);

    done();
  });

  it('should ignore feedback from non current searches', (done) => {
    const parsedData = 'and_comm forall A B : Prop, A /\\ B <-> B /\\ A ';
    const expectedName = 'and_comm';

    // current tag is search-1 but currentSearch is still 0
    serapi.currentTag = 'search-1';
    serapi.callbacks.set(serapi.currentTag, {onResult: () => {}});
    serapi.handleSearchFeedback(parsedData);
    expect(serapi.searchResults.has(expectedName)).to.equal(false);

    done();
  });
});
