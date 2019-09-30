'use strict';


/**
 * The interface that Waterproof uses to communicate with Coq
 */
class CoqInterface {
  /**
   * CoqInterface (no implementation)
   */
  constructor() {
  }

  /**
   * Sets the Coq content to the given string.
   *
   * @param {string} content The Coq code to set the content to.
  */
  setContent(content) {
  }

  /**
   * Executes Coq code until the provided index
   *
   * @param {Number} index The index of the cursor
   */
  executeTo(index) {
  }

  /**
   * Executes the next Coq sentence
   */
  executeNext() {
  }

  /**
   * Rolls back the last Coq sentence
   */
  executePrevious() {
  }

  /**
     * Gets the goals at the given index,
     * when no index supplied this is after the last executed sentence
     *
     * @param {Number} index  The index in the file
     * @param {function} onSuccess The callback function on succes
     * @param {function} onError The callback funcion on error
     * @async
     */
  getGoals(index, onSuccess, onError) {
  }

  /**
   * Gets the search results for a given searchquery.
   * Might want to move this to a different serapi
   *
   * [TODO: Check search restrictions]
   *
   * @param {String} searchQuery Query to search for
   * @param {Function} onResult callback for when a search result has been found
   * @param {Function} onDone callback for when searching is done
   */
  getSearchResults(searchQuery, onResult, onDone) {
  }

  /**
   * Stop this instance of coq
   */
  stop() {
  }
}

export default CoqInterface;
