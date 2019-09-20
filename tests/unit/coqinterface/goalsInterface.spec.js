import CoqSerapi from '../../../src/coq/serapi/CoqSerapi';
import SerapiInterface from '../../../src/coq/serapi/SerapiInterface';
import EditorInterface from '../../../src/coq/EditorInterface';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('getGoals', () => {
  // Replace all the functions of the interface with SerAPI by fakes
  // See https://sinonjs.org/releases/v7.3.2/fakes/
  const serapi = new SerapiInterface;
  const callbacks = new EditorInterface;

  let impl;

  // Before each test, reset the call counts etc. of all the fake functions
  beforeEach(() => {
    sandbox.replace(serapi, 'add', sinon.fake());
    sandbox.replace(serapi, 'cancel', sinon.fake());
    sandbox.replace(serapi, 'exec', sinon.fake());
    sandbox.replace(serapi, 'goals', sinon.fake());
    impl = new CoqSerapi(serapi, callbacks);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should reject calls with index less than 0', (done) => {
    const shouldThrow = () => {
      impl.getGoals(-1, () => { }, () => { });
    };
    expect(shouldThrow).to.throw();
    expect(serapi.goals.callCount).to.be.equal(0);
    done();
  });

  it('should reject calls with index out of content', (done) => {
    const content = 'Proof.';
    impl.setContent(content, () => { }, () => { });
    const shouldThrow = () => {
      impl.getGoals(content.length + 1, () => { }, () => { });
    };
    expect(shouldThrow).to.throw();
    expect(serapi.goals.callCount).to.be.equal(0);
    done();
  });

  it('should call the "goals" method of the interface with the correct sid',
      (done) => {
        const text = 'Lemma a5: forall n: nat, n + 0 = n. Proof.';
        const lastSentenceId = 3; // `text` has sentence IDs 2 and 3
        impl.setContent(text, () => { }, () => { });
        impl.sentences.sentences = [
          {sentenceId: 2, beginIndex: 0, endIndex: 35},
          {sentenceId: 3, beginIndex: 36, endIndex: 42}];
        impl.currentContent = text;
        impl.getGoals(text.length, () => { }, () => { });
        expect(serapi.goals.callCount).to.be.equal(1);
        expect(serapi.goals.lastCall.args[0]).to.be.equal(lastSentenceId);
        done();
      });

  it('should throw an error if the sentence index is out of bounds', (done) => {
    const shouldThrow = () => {
      impl.getGoalsAtSentence(-1, () => { }, () => { });
    };
    expect(shouldThrow).to.throw();
    expect(serapi.goals.callCount).to.be.equal(0);
    done();
  });
});
