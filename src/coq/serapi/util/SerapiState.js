import {Mutex} from 'async-mutex';
import CoqState from '../../CoqState';

/**
 * Class for holding all the shared state of an active serapi! instance
 * This includes:
 *  - Sentences (id, begin, end, ast, ...)
 *  - execution (execution state, targets, ...)
 *  Implements CoqState
 */
class SerapiState extends CoqState {
  /**
   * Constructor of SerapiState
   */
  constructor() {
    super();
    this.stateLock = new Mutex();
    this.executionLock = new Mutex();

    this.sentences = [];

    this.lastExecuted = -1;
    this.target = -1;
  }

  /**
   * Get the sentence at the index
   * @param {Number} index
   * @return {Object} the sentence
   */
  getSentenceByIndex(index) {
    return this.sentences[index];
  }

  /**
   * Append sentences at the end
   * @param {Array} sentences the sentences to concat
   */
  concatSentences(sentences) {
    this.sentences = this.sentences.concat(sentences);
  }

  /**
   * Add a sentence with the given id, begin, end, text content and ast
   * @param {Number} sentenceId the sentence id
   * @param {Number} beginIndex the begin index
   * @param {Number} endIndex the end index
   * @param {String} text the textual content
   * @param {*} ast The AST
   */
  addSentence(sentenceId, beginIndex, endIndex, text, ast) {
    if (sentenceId == null || beginIndex == null || endIndex == null) {
      throw new Error('Sentence must have at least id, bi, ei');
    }
    this.sentences.push({
      sentenceId,
      beginIndex,
      endIndex,
      text: text == null ? null : text,
      ast: ast == null ? null : ast,
    });
  }

  /**
   * Get the begin index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  beginIndexOfSentence(index) {
    return this.sentences[index].beginIndex;
  }

  /**
   * Get the end index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the end index
   */
  endIndexOfSentence(index) {
    return this.sentences[index].endIndex;
  }

  /**
   * Get the sentence id of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  idOfSentence(index) {
    return this.sentences[index].sentenceId;
  }

  /**
   * Get the text of a sentence
   * @param {Number} index the index of the sentence
   * @return {String} the text of that sentence
   */
  textOfSentence(index) {
    return this.sentences[index].text;
  }

  /**
   * Adorn the sentence with sentenceId sid with
   * an AST
   * @param {Number} sid  sentenceId of the sentence
   * @param {Object} ast  The AST of the sentence
   */
  setASTforSID( sid, ast ) {
    const index = this.indexOfSentence(sid);
    if (index < 0) {
      return;
    }
    this.sentences[index].ast = ast;
  }

  /**
   * Get the AST of the sentence
   * @param {Number} index the index of the sentence
   * @return {*} the AST or undefined if not loaded
   */
  getASTOfSentence(index) {
    return this.sentences[index].ast;
  }

  /**
   * Get the sentence index for a given sentenceId
   * TODO: optimize
   * @param {Number} sid  The sentenceId of the sentence
   * @return {Number}  The index in the sentences array
   * containing the sentence with the requested sid
   */
  indexOfSentence(sid) {
    for (let j = 0; j < this.sentences.length; j++ ) {
      if (this.sentences[j].sentenceId === sid) {
        return j;
      }
    }
    return -1;
  }

  /**
   * Get the amount of sentences
   * @return {Number} the amount
   */
  sentenceSize() {
    return this.sentences.length;
  }

  /**
   * Remove all sentences after index
   * @param {Number} index from where to remove
   */
  removeSentencesAfter(index) {
    this.sentences = this.sentences.slice(0, index);
  }

  /**
   * Remove sentence with sid
   * @param {Number} sid the Sentence id
   */
  removeSentence(sid) {
    const index = this.indexOfSentence(sid);
    if (index < 0) {
      return;
    }
    this.sentences.splice(index, 1);
  }

  /**
   * Get the sentence that finishes just before the index
   * @param {Number} index the index in the content
   * @return {undefined|number} the sentence before the content
   */
  sentenceBeforeIndex(index) {
    if (this.sentenceSize() === 0) {
      return -1;
    }

    const lastSentence = this.sentenceSize() - 1;

    if (this.endIndexOfSentence(lastSentence) <= index) {
      return lastSentence;
    }

    for (let i = 0; i <= lastSentence; i++) {
      const end = this.endIndexOfSentence(i);

      if (index < end) {
        return i - 1;
      }
    }
    return -1;
  }

  /**
   * Get the first sentence that starts after the index
   * @param {Number} index the index in the content
   * @return {*} the first sentence after that index
   */
  sentenceAfterIndex(index) {
    for (let i = 0; i < this.sentenceSize(); i++) {
      const sentence = this.getSentenceByIndex(i);
      if (index < this.beginIndexOfSentence(i)) {
        return {
          index: i,
          sentence,
        };
      }
    }
    return null;
  }

  /**
   * Extract the corresponding string from the provided text by
   * using location data stored in this SerapiSentences object.
   * @param {String} text  The text to find the sentence in
   * @param {Number} sentenceNr  The number of the sentence
   * @return {String} The extracted sentence
   */
  getSentenceAsString(text, sentenceNr) {
    return text.slice(this.sentences[sentenceNr].beginIndex,
        this.sentences[sentenceNr].endIndex);
  }

  /**
   * TEMP
   * @param {Number} index a
   * @return {null}
   */
  getFlatAST(index) {
    if (this.sentences[index].ast == null) {
      return null;
    }
    if (this.sentences[index].flatAst == null) {
      let i = 0;
      this.sentences[index].flatAst = this.sentences[index].text
          .slice(0, this.sentences[index].text.length - 1)
          .split(' ')
          .map((str) => {
            const start = i;
            i += str.length;
            const end = i;
            i++;
            return {
              start,
              end,
              type: str,
            };
          });
    }
    return this.sentences[index].flatAst;
  }
}

export default SerapiState;
