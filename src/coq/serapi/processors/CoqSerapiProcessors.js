'use strict';

import CoqInterface from '../../CoqInterface';
import SerapiState from '../util/SerapiState';
import SerapiContentProcessor from './SerapiContentProcessor';
import SerapiTagger from '../SerapiTagger';
import SerapiExecutionProcessor from './SerapiExecutionProcessor';
import SerapiSearchProcessor from './SerapiSearchProcessor';

/**
 * The main interface to SerAPI. An implementation of CoqInterface
 */
class CoqSerapiProcessors extends CoqInterface {
  /**
   * Create a CoqSerapiProcessors with the given worker and editor callbacks
   * @param {SerapiWorker} worker
   * @param {EditorInterface} editor
   */
  constructor(worker, editor) {
    super();

    this.ready = false;
    this.stopped = false;

    this.worker = worker;

    this.state = new SerapiState();
    this.tagger = new SerapiTagger(worker, () => {
      if (!this.stopped) {
        this.ready = true;
        editor.onReady();
      } else {
        this.worker.terminate();
      }
    });
    this.contentProcessor =
        new SerapiContentProcessor(this.tagger, this.state, editor);
    this.executionProcessor =
        new SerapiExecutionProcessor(this.tagger, this.state, editor);
    this.searchProcessor =
        new SerapiSearchProcessor(this.tagger, this.state, editor);
  }

  /**
   * Sets the Coq content to the given string.
   *
   * @param {string} content The Coq code to set the content to.
   * @return {Promise} which resolves when the execution is set/started
   */
  setContent(content) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.contentProcessor.setContent(content);
  }

  /**
   * Executes the next Coq sentence
   * @return {Promise} which resolves when the execution is done/started
   */
  executeNext() {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executeNext();
  }

  /**
   * Rolls back the last Coq sentence
   * @return {Promise} which resolves when the execution is done/started
   */
  executePrevious() {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executePrevious();
  }

  /**
   * Executes Coq code until the provided index
   *
   * @param {Number} index The index of the cursor
   * @return {Promise} which resolves when the execution is done/started
   */
  executeTo(index) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executeTo(index);
  }

  /**
   * Gets the goals at the given index,
   * when no index supplied this is after the last executed sentence
   *
   * @param {Number} index  The index in the file
   * @param {function} onSuccess The callback function on succes
   * @param {function} onError The callback funcion on error
   * @async
   * @return {Promise} which resolves with the goal when received
   */
  getGoals(index, onSuccess, onError) {
    return Promise.reject(new Error('not implemented'));
  }

  /**
   * Gets the search results for a given searchquery.
   *
   *
   * @param {String} searchQuery Query to search for
   * @param {Function} onResult callback for when a search result has been found
   * @param {Function} onDone callback for when searching is done
   * @async
   * @return {Promise} which resolves when the search is complete
   */
  getSearchResults(searchQuery, onResult, onDone) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.searchProcessor.searchFor(searchQuery, onResult, onDone);
  }

  /**
   * Stop this instance of serapi
   */
  stop() {
    this.stopped = true;
    if (this.ready) {
      this.ready = false;
      this.worker.terminate();
    }
  }

  /**
   * Get the current state
   * @return {CoqState} the current coq state
   */
  getState() {
    return this.state;
  }
}

export default CoqSerapiProcessors;
