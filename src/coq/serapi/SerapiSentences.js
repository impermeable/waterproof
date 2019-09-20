/**
 * Holds sentenecs from serapi
 */
class SerapiSentences {
  /**
   * Holds sentenecs from serapi
   */
  constructor() {
    this.sentences = [];
  }

  /**
   * Get the sentence at the index
   * @param {Number} index
   * @return {Object} the sentence
   */
  get(index) {
    return this.sentences[index];
  }

  /**
   * Replace the sentence
   * @param {Number} index the index where to replace
   * @param {Object} sentence the new sentence
   */
  set(index, sentence) {
    this.sentences.splice(index, 1, sentence);
  }

  /**
   * Append sentences at the end
   * @param {Array} sentences the sentences to concat
   */
  concat(sentences) {
    this.sentences = this.sentences.concat(sentences);
  }

  /**
   * Get the begin index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  beginIndex(index) {
    return this.sentences[index].beginIndex;
  }

  /**
   * Get the end index of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the end index
   */
  endIndex(index) {
    return this.sentences[index].endIndex;
  }

  /**
   * Get the sentence id of a sentence
   * @param {Number} index the index of the sentence
   * @return {number} the begin index
   */
  id(index) {
    return this.sentences[index].sentenceId;
  }

  /**
   * Adorn the sentence with sentenceId sid with
   * an AST
   * @param {Number} sid  sentenceId of the sentence
   * @param {Object} ast  The AST of the sentence
   */
  setASTforSID( sid, ast ) {
    const id = this.index(sid);
    if ( id !== -1 ) {
      this.sentences[id].ast = ast;
    }
  }

  /**
   * Get the sentence index for a given sentenceId
   * @param {Number} sid  The sentenceId of the sentence
   * @return {Number}  The index in the sentences array
   * containing the sentence with the requested sid
   */
  index(sid) {
    for (let j = 0; j < this.sentences.length; j++ ) {
      if (this.sentences[j].sentenceId == sid) {
        return j;
      }
    }
    return -1;
  }

  /**
   * Get the amount of sentences
   * @return {Number} the amount
   */
  length() {
    return this.sentences.length;
  }

  /**
   * Remove all sentences after index
   * @param {Number} index from where to remove
   */
  removeAfter(index) {
    this.sentences = this.sentences.slice(0, index);
  }

  /**
   * Get the sentence that finishes just before the index
   * @param {Number} index the index in the content
   * @return {undefined|number} the sentence before the content
   */
  sentenceBeforeIndex(index) {
    if (this.length() === 0) {
      return -1;
    }

    const lastSentence = this.length() - 1;

    if (this.endIndex(lastSentence) <= index) {
      return lastSentence;
    }

    for (let i = 0; i <= lastSentence; i++) {
      const end = this.endIndex(i);

      if (index < end) {
        return i - 1;
      }
    }
    return -1;
  }

  /**
   * Get the first sentence that starts after the index
   * @param {Number} index the index in the content
   * @return {null|Sentence} the first sentence after that index
   */
  sentenceAfterIndex(index) {
    for (let i = 0; i < this.length(); i++) {
      const sentence = this.get(i);
      if (index < this.beginIndex(i)) {
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
    const returnText = text.slice(this.sentences[sentenceNr].beginIndex,
        this.sentences[sentenceNr].endIndex);
    return returnText;
  }
}

export default SerapiSentences;
