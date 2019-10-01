'use strict';

import CoqInterface from '../../CoqInterface';
import SerapiState from '../util/SerapiState';
import SerapiContentProcessor from './SerapiContentProcessor';
import SerapiTagger from '../SerapiTagger';
import SerapiExecutionProcessor from './SerapiExecutionProcessor';
import SerapiSearchProcessor from './SerapiSearchProcessor';

/**
 * The main interface to SerAPI. Exposes a JavaScript interface where commands
 * are sent with onSuccess and onError handlers, one of which will be called
 * when SerAPI's responses to the command come in.
 */
class CoqSerapiProcessors extends CoqInterface {
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

  setContent(content) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.contentProcessor.setContent(content);
  }

  executeNext() {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executeNext();
  }

  executePrevious() {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executePrevious();
  }

  executeTo(index) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.executionProcessor.executeTo(index);
  }

  getGoals(index, onSuccess, onError) {
    return Promise.reject(new Error('not implemented'));
  }

  getSearchResults(searchQuery, onResult, onDone) {
    if (!this.ready) {
      return Promise.resolve();
    }
    return this.searchProcessor.searchFor(searchQuery, onResult, onDone);
  }

  stop() {
    this.stopped = true;
    if (this.ready) {
      this.ready = false;
      this.worker.terminate();
    }
  }
}

export default CoqSerapiProcessors;
