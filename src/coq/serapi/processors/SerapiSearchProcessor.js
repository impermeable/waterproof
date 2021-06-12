import SerapiProcessor from '../util/SerapiProcessor';
import {Mutex} from 'async-mutex';
import {
  createCheckCommand, createQueryVernacCommand,
  createSearchCommand,
} from '../util/SerapiCommandFactory';
import {COQ_EXCEPTION, parseErrorResponse} from '../SerapiParser';

/**
 * Process search results
 * @param {*} result the search result
 * @param {Function} onResult function to call with every (new) result
 * @param {[]} ignoredResults list of already received results/results that
 *   should be ignored
 * @private
 */
function _processResults(result, onResult, ignoredResults) {
  if (Object.prototype.hasOwnProperty.call(result, 'error')) {
    return;
  }

  for (const [key, value] of Object.entries(result)) {
    if (ignoredResults.indexOf(key) < 0) {
      onResult(value);
      ignoredResults.push(key);
    }
  }
}

/**
 * Processor for searching
 */
class SerapiSearchProcessor extends SerapiProcessor {
  /**
   * Create a SerapiSearchProcessor
   * @param {SerapiTagger} tagger the tagger to use
   * @param {SerapiState} state the state to use
   * @param {EditorInterface} editor the editor to use
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);

    this.currentSearch = 0;
    this.searchNumLock = new Mutex();
  }


  /**
   * Search for a query
   * Sends a check, search and string based search
   * @param {String} query the search query
   * @param {Function} onResult called for every result
   * @param {Function} onDone called when all results are send
   * @return {Promise<void>}
   */
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

  /**
   * Send a command via vernac
   * @param {String} command the command
   * @return {Promise<void>} resolved when the command is complete
   */
  async query(command) {
    const noExecution = await this.state.executionLock.acquire();

    const releaseContent = await this.state.stateLock.acquire();
    noExecution();

    await this._queryCommand(command);

    releaseContent();
  }

  /**
   * Start a new search (increment current search)
   * @return {Promise<number>} the number of the new search
   * @private
   */
  async _startNewSearch() {
    const release = await this.searchNumLock.acquire();
    if (this.currentSearch > 100000) {
      this.currentSearch = -1;
    }
    const newSearch = ++this.currentSearch;
    release();
    return newSearch;
  }

  /**
   * Check if this search is still the most current and can continue
   * @param {Number} searchNumber the number of the search
   * @return {Promise<boolean>} whether it can continue
   * @private
   */
  async _continueSearch(searchNumber) {
    const release = await this.searchNumLock.acquire();
    const stillCurrent = this.currentSearch === searchNumber;
    release();
    return stillCurrent;
  }

  /**
   * Handle a serapi feedback
   * @param {*} feedback the serapi feedback (parsed)
   * @return {*} partial of this command
   */
  handleResultFeedback(feedback) {
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

  /**
   * Send the check query
   * @param {String} query the search query
   * @param {Function} onResult function to be called with every result
   * @param {[]} ignored array of already received results
   * @return {Promise<*>} promise which resolves when command complete
   * @private
   */
  async _checkQuery(query, onResult, ignored) {
    return this.sendCommand(createCheckCommand(query), 'c',
        this.handleResultFeedback)
        .then((result) => _processResults(result, onResult, ignored));
  }

  /**
   * Send the search query
   * @param {String} query the search query
   * @param {Function} onResult function to be called with every result
   * @param {[]} ignored array of already received results
   * @return {Promise<*>} promise which resolves when command complete
   * @private
   */
  async _searchQuery(query, onResult, ignored) {
    return this.sendCommand(createSearchCommand('(' + query + ')'), 'q',
        this.handleResultFeedback)
        .then((result) => _processResults(result, onResult, ignored));
  }

  /**
   * Send the search in string query
   * @param {String} query the search query
   * @param {Function} onResult function to be called with every result
   * @param {[]} ignored array of already received results
   * @return {Promise<*>} promise which resolves when command complete
   * @private
   */
  async _searchStringQuery(query, onResult, ignored) {
    return this.sendCommand(createSearchCommand('"' + query + '"'), 't',
        this.handleResultFeedback)
        .then((result) => _processResults(result, onResult, ignored));
  }

  /**
   * Send a command with vernac
   * @param {String} command the command
   * @return {Promise<*|Promise<unknown>>}
   * @private
   */
  async _queryCommand(command) {
    return this.sendCommand(createQueryVernacCommand(command), 'raw',
        (feedback) => {
          return {
            result: feedback.string,
          };
        })
        .then((result) => {
          if (Object.prototype.hasOwnProperty.call(result, 'result')) {
            this.editor.message(result.result);
          }
          if (result.error) {
            this.editor.message(result.errorMessage);
          }
        });
  }

  /**
   * Handle a serapi message
   * @param {*} data the serapi message (parsed)
   * @param {String} extraTag the extra identifying tag
   * @return {*} partial of this command
   */
  handleSerapiMessage(data, extraTag) {
    // this is not actually needed but used in case?? results come in and an
    // error occurred
    if (data.length > 0 && data[0] === COQ_EXCEPTION) {
      return {
        error: true,
        errorMessage: parseErrorResponse(data).message,
      };
    }
  }
}


export default SerapiSearchProcessor;
