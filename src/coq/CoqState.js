/* eslint-disable valid-jsdoc */
/**
 * Class for holding all the shared state of an active coq instance
 * This includes:
 *  - Sentences (id, begin, end, ast, ...)
 *  - execution (execution state, targets, ...)
 */

class CoqState {
  constructor() {
  }

  /**
   * Get the sentence at the index
   * @param {Number} index
   * @return {Object} the sentence
   */
  getSentenceByIndex(index) {
  }

  /**
   * Append sentences at the end
   * @param {Array} sentences the sentences to concat
   */
  concatSentences(sentences) {
  }

  addSentence(sentenceId, beginIndex, endIndex, text, ast) {
  }

  /**
   * Get the begin index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  beginIndexOfSentence(index) {
  }

  /**
   * Get the end index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the end index
   */
  endIndexOfSentence(index) {
  }

  /**
   * Get the sentence id of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  idOfSentence(index) {
  }

  /**
   * Get the text of a sentence
   * @param {Number} index the index of the sentence
   * @return {String} the text of that sentence
   */
  textOfSentence(index) {
  }


  /**
   * Get the sentence index for a given sentenceId
   * TODO: optimize
   * @param {Number} sid  The sentenceId of the sentence
   * @return {Number}  The index in the sentences array
   * containing the sentence with the requested sid
   */
  indexOfSentence(sid) {
  }

  /**
   * Get the amount of sentences
   * @return {Number} the amount
   */
  sentenceSize() {
  }

  /**
   * Remove all sentences after index
   * @param {Number} index from where to remove
   */
  removeSentencesAfter(index) {
  }

  /**
   * Remove sentence with sid
   * @param {Number} sid the Sentence id
   */
  removeSentence(sid) {
  }

  /**
   * Get the sentence that finishes just before the index
   * @param {Number} index the index in the content
   * @return {undefined|number} the sentence before the content
   */
  sentenceBeforeIndex(index) {
  }

  /**
   * Get the first sentence that starts after the index
   * @param {Number} index the index in the content
   * @return {null|Sentence} the first sentence after that index
   */
  sentenceAfterIndex(index) {
  }

  /**
   * Extract the corresponding string from the provided text by
   * using location data stored in this SerapiSentences object.
   * @param {String} text  The text to find the sentence in
   * @param {Number} sentenceNr  The number of the sentence
   * @return {String} The extracted sentence
   */
  getSentenceAsString(text, sentenceNr) {
  }
}

export default CoqState;
