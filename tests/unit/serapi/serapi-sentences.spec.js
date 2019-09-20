import SerapiSentences from '../../../src/coq/serapi/SerapiSentences.js';

const chai = require('chai');
const expect = chai.expect;

describe('serapi add response handler', () => {
  let sentences;

  beforeEach(() => {
    sentences = new SerapiSentences;
  });

  const createSentence = (id=0, bi=0, ei=10) => {
    return {
      sentenceId: id,
      beginIndex: bi,
      endIndex: ei,
    };
  };

  it('should start with no sentences', (done) => {
    expect(sentences.length()).to.equal(0);
    done();
  });

  it('should add sentences', (done) => {
    const sentence = createSentence();
    sentences.concat([sentence]);
    expect(sentences.length()).to.equal(1);
    expect(sentences.get(0)).to.equal(sentence);

    done();
  });

  it('should replace a sentence', (done) => {
    const oldSentence = createSentence();
    const newSentence = createSentence(1);
    sentences.concat([oldSentence]);
    expect(sentences.length()).to.equal(1);
    sentences.set(0, newSentence);
    expect(sentences.length()).to.equal(1);
    expect(sentences.get(0)).to.equal(newSentence);

    done();
  });

  const testAfterIndex = (selectedIndex) => {
    const firstSentence = createSentence(0, 0, 10);
    const secondSentence = createSentence(1, 10, 20);
    sentences.concat([firstSentence, secondSentence]);

    return sentences.sentenceAfterIndex(selectedIndex);
  };

  it('should give the right sentence with after index at -1', (done) => {
    const selectedSentence = testAfterIndex(-1);

    expect(selectedSentence.index).to.equal(0);

    done();
  });

  it('should give the right sentence with after index at 0', (done) => {
    const selectedSentence = testAfterIndex(0);

    expect(selectedSentence.index).to.equal(1);

    done();
  });

  it('should give null after last sentence with after index', (done) => {
    const selectedSentence = testAfterIndex(11);

    expect(selectedSentence).to.equal(null);

    done();
  });

  it('should give null at end of text with after index', (done) => {
    const selectedSentence = testAfterIndex(20);

    expect(selectedSentence).to.equal(null);

    done();
  });
});
