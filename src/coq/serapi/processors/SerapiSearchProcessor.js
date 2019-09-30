import SerapiProcessor from '../util/SerapiProcessor';
import {Mutex} from 'async-mutex';
import {
  createCheckCommand,
  createSearchCommand,
} from '../util/SerapiCommandFactory';
import * as Constants from '../SerapiConstants';

class SerapiSearchProcessor extends SerapiProcessor {
  /**
   *
   * @param {SerapiTagger} tagger
   * @param {SerapiState} state
   * @param {EditorInterface} editor
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);

    this.currentSearch = 0;
    this.searchNumLock = new Mutex();
  }


  async searchFor(query, onResult, onDone) {
    const searchNum = await this._startNewSearch();
    // make sure the search number is updated before 'starting'

    // ensure no execution is taking place
    const noExecution = await this.state.executionLock.acquire();

    const releaseContent = await this.state.stateLock.acquire();
    noExecution();

    const results = [];

    await this._checkQuery(query, onResult, results);

    if (!await this._continueSearch(searchNum)) {
      releaseContent();
      return;
    }

    await this._searchQuery(query, onResult, results);

    if (!await this._continueSearch(searchNum)) {
      releaseContent();
      return;
    }

    await this._searchStringQuery(query, onResult, results);

    // TODO: should we really check here?
    if (!await this._continueSearch(searchNum)) {
      releaseContent();
      return;
    }

    releaseContent();
    onDone();
    return Promise.resolve();
  }

  async _startNewSearch() {
    const release = await this.searchNumLock.acquire();
    if (this.currentSearch > 100000) {
      this.currentSearch = -1;
    }
    const newSearch = ++this.currentSearch;
    release();
    return newSearch;
  }

  async _continueSearch(searchNumber) {
    const release = await this.searchNumLock.acquire();
    const stillCurrent = this.currentSearch === searchNumber;
    release();
    return stillCurrent;
  }

  _processResults(result, onResult, ignoredResults) {
    if (result.hasOwnProperty('error')) {
      return;
    }

    for (const [key, value] of Object.entries(result)) {
      if (ignoredResults.indexOf(key) < 0) {
        onResult(value);
        ignoredResults.push(key);
      }
    }
  }

  async _checkQuery(query, onResult, ignored) {
    return this.sendCommand(createCheckCommand(query), 'c')
        .then((result) => this._processResults(result, onResult, ignored));
  }

  async _searchQuery(query, onResult, ignored) {
    return this.sendCommand(createSearchCommand('(' + query + ')'), 'q')
        .then((result) => this._processResults(result, onResult, ignored));
  }

  async _searchStringQuery(query, onResult, ignored) {
    return this.sendCommand(createSearchCommand('"' + query + '"'), 't')
        .then((result) => this._processResults(result, onResult, ignored));
  }

  handleSerapiMessage(data, extraTag) {
    // this is not actually needed but used in case?? results come in and an
    // error occurred
    if (data.length > 0 && data[0] === Constants.COQ_EXCEPTION) {
      return {
        error: true,
      };
    }
  }

  handleSerapiFeedback(feedback, extraTag) {
    const feedbackText = feedback.string;

    let resultName = feedbackText.split(' ', 1)[0];

    if (resultName === 'Error:' || resultName.indexOf('?') > -1) {
      return;
    }

    if (resultName.endsWith(':')) {
      resultName = resultName.substr(0, resultName.length - 1);
    }

    let resultData = feedbackText.substring(resultName.length + 1).trim();
    if (resultData[0] === ':') {
      resultData = resultData.substring(1).trim();
    }
    // TODO: do onResult call here?

    return {
      [resultName]: {
        name: resultName,
        content: resultData,
      },
    };
  }
}


export default SerapiSearchProcessor;
