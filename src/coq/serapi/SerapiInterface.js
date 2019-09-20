'use strict';

/**
 * Class that interface with serapi in some way
 */
class SerapiInterface {
  /**
   * Interface (non implementation) of SerapiCommands
   */
  constructor() {
  }

  /**
   * Add code to the document
   * @param {String} code the code to add
   * @param {Function} onSuccess callback which is called when this is added,
   *   with mapping to sentence id?
   * @param {Function} onError if add fails (obvious parse error), and
   *   sentences that were added
   */
  add(code, onSuccess, onError) {
  }

  /**
   * Cancel sentence `sentence` (might implicitly cancel previous sentences)
   * @param {Number} sentenceId the sentence id(s) to cancel
   * @param {Function} onSuccess callback which is called if the cancel is a
   * success with which sentences were cancelled
   * @param {Function} onError callback for errors (never?)
   */
  cancel(sentenceId, onSuccess, onError) {
  }

  /**
   * Execute code upto and including the sentence
   * @param {Number} sentenceId the sentence id to where to execute
   * @param {Function} onSuccess callback with goal, sentence to where the
   *  code was executed (note that this only calls at the end, for incremental
   *  executing call multiple times)
   * @param {Function} onError if there is some error e.g. execution failed,
   *   or does not exist will give the error in text, the sentence where the
   *   error occured, the sentence to where execution passed, and the goal
   *   just before the error
   */
  exec(sentenceId, onSuccess, onError) {
  }

  /**
   * Get the goal at a certain sentence
   * @param {Number} sentenceId the sentence id where to get the goal from
   * @param {Function} onSuccess callback with the goal
   * @param {Function} onError callback on failure
   *   (not executed id, non existing id)
   * @param {String} format the format to use
   */
  goals(sentenceId, onSuccess, onError, format) {
  }

  /**
   * Request to serAPI the Abstract Syntax Tree (AST) of a sentence.
   * @param {Number} sentenceNr The number of the sentence
   * @param {Function} onSuccess  What should happen on success
   * @param {Function} onError  What should happen on error
   */
  requestAST(sentenceNr, onSuccess, onError) {
  }

  /**
   * Get searchresult(s)
   * @param {String} searchQuery The query to use for searching
   * @param {Function} onSuccess The callback for new search results
   * @param {Function} onError The callback for errors
   */
  search(searchQuery, onSuccess, onError) {
  }

  /**
   * Whether this serapi interface is ready to send commands
   *
   * @return {Boolean} true when ready
   */
  isReady() {
    return true;
  }

  /**
   * Stop this instance of coq
   */
  terminate() {
  }
}

export default SerapiInterface;
