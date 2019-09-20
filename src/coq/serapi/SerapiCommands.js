/* eslint-disable no-console */
'use strict';

import SerapiInterface from './SerapiInterface';

const parse = require('s-expression');
const flatten = require('./flatten-expr').flatten;
const byteIndexToStringIndex = require('./StringIndices')
    .byteIndexToStringIndex;

// const traverseArray = require('./ASTProcessor').traverseArray;
const extractAST = require('./ASTProcessor').extractCoqAST;

import * as Constants from './SerapiConstants';
import {parseFeedback, parseErrorResponse, sanitise} from './SerapiParser';

/**
 * Implementation of Serapi interface using the js worker;
 */
class SerapiCommands extends SerapiInterface {
  /*
   * The `callbacks` map contains for each command tag a pair
   * (onSuccess, onError). When, for example, the function
   * setContent(content, onSuccess, onError) is called, the following is done:
   *  1. A tag is created for this command (as a hash of the content, a
   *      counter, whatever)
   *  2. The onSuccess and onError functions are saved in this hashmap under
   *      the correct tag
   *  3. The correct command is sent to SerAPI
   *  4. When SerAPI gives back output, the output handler can use the tag to
   *      call the correct callback function
   *  5. When the output for this command is done, indicated by
   *      (Answer ... completed), the callbacks are removed from the map
   */

  /**
   * Create a js worker based serapi interface
   * @param {SerapiWorker} worker the worker
   * @param {function} messageCallback call to transfer messages
   * @param {Function} onReadyCallback call when serapi is ready
   */
  constructor(worker,
      messageCallback, onReadyCallback) {
    super();
    if (worker !== null) {
      this.worker = worker;
      this.worker.onMessage = (m) => this.handleMessage(m);
    }

    this.ready = false;
    this.currentMessageNumber = 0;

    this.addLog = {};
    this.astLog = {};

    this.callbacks = new Map();
    this.callbackData = new Map();

    this.messageCallback = messageCallback;
    this.onReadyCallback = onReadyCallback;

    this.currentTag = null;
    this.currentSearch = 0;
    this.searchesCompleted = 0;
    this.searchResults = new Map();
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
    // TODO the max sentence id is 2^31-1 so newtip might need to be set
    // VERY IMPORTANT!!
    const sanitizedCode = sanitise(code);
    const message = `(Add () "${sanitizedCode}")`;

    const tagId = this.postMessage(message,
        Constants.ADD_COMMAND, {onSuccess, onError});
    this.addLog[tagId] = code;
  }

  /**
   * Cancel sentence `sentence` (might implicitly cancel previous sentences)
   * @param {object} sentence the sentence id(s) to cancel
   *   (can be int, string, array)
   * @param {Function}onSuccess callback which is called if the cancel
   *   is a success with which sentences were cancelled
   * @param {Function} onError callback for errors (never?)
   */
  cancel(sentence, onSuccess, onError) {
    // console.log(`cancel ${sentence}`);
    let message;
    if (Array.isArray(sentence)) {
      const sentencesList = sentence.join(' ');
      message = `(Cancel (${sentencesList}))`;
    } else {
      message = `(Cancel (${sentence}))`;
    }

    this.postMessage(message, Constants.CANCEL_COMMAND, {onSuccess, onError});
  }

  /**
   * Execute sentence (will probably execute sentences before that sentence)
   * @param {Number} sentence the sentence id to execute
   * @param {Function} onSuccess callback with sentences that were executed
   *   (note that this only calls at the end, for incremental executing
   *    call multiple times)
   * @param {Function} onError if there is some error e.g. execution failed,
   *  or does not exist  will give the error in text, the sentence where
   *  the error occurred, the sentence to where execution passed, and the goal
   *  just before the error
   */
  exec(sentence, onSuccess, onError) {
    // console.log(`exec ${sentence}`);
    const cmd = `(Exec ${sentence})`;
    this.postMessage(cmd, Constants.EXEC_COMMAND, {onSuccess, onError});
  }

  /**
   * Get the goal at a certain sentence
   * @param {Number} sentence the sentence id where to get the goal from
   * @param {Function} onSuccess callback with the goal
   * @param {Function} onError callback on failure
   *   (not executed id, non existing id)
   * @param {String} format the format to give to serapi
   */
  goals(sentence, onSuccess, onError, format = 'PpStr') {
    // console.log(`goal ${sentence}`);
    const cmd = `(Query ((sid ${sentence})`
              + `(pp ((pp_format ${format})))) Goals)`;
    this.postMessage(cmd, Constants.GOAL_COMMAND, {onSuccess, onError});
  }

  /**
   * Get searchresult(s)
   * @param {String} searchQuery The query to use for searching
   * @param {Function} onResult The callback for new search results
   * @param {Function} onSuccess The callback for when searching is done
   */
  search(searchQuery, onResult, onSuccess) {
    console.log(`search ${searchQuery}`);
    const tag = Constants.SEARCH_COMMAND + '-' + (++this.currentSearch);

    this.searchResults.clear();
    this.searchesCompleted = 0;

    const checkSearch =
      `(Query () (Vernac "Check (${searchQuery})."))`;
    this.postMessage(checkSearch, tag, {onResult, onSuccess});

    const patternSearch =
      `(Query () (Vernac "Search (${searchQuery})."))`;
    this.postMessage(patternSearch, tag, {onResult, onSuccess});

    const stringSearch =
      `(Query () (Vernac "Search \\"${searchQuery}\\"."))`;
    this.postMessage(stringSearch, tag, {onResult, onSuccess});
  }

  /**
   * Executes a Coq vernac query
   * @param {string} inputQuery The vernac query to execute
   */
  query(inputQuery) {
    console.log(`query ${inputQuery}`);
    const query = `(Query() (Vernac "${inputQuery}"))`;
    this.postMessage(query, Constants.QUERY_COMMAND,
        {onSuccess: null, onError: null});
  }

  /**
   * Checks whether the given input belongs to a lemma or definition
   * @param {string} name The name of the definition or lemma
   * @param {string} data The definition or lemma itself
   */
  checkType(name, data) {
    const tag = Constants.CHECK_COMMAND + '-' + name;
    const query = `(Query () (Vernac "Check (${data})."))`;
    this.postMessage(query, tag, this.callbacks.get(this.currentTag));
  }

  /**
   * Post a message to SerAPI and prepare the associated callbacks
   * @param {string} message The message to pass to SerAPI
   * @param {string} tag The tag to identify the message by
   * @param {Object} callbacks The onSuccess and onError callbacks
   * @return {Number} The tagId that was given out to the message
   */
  postMessage(message, tag, callbacks) {
    const tagId = this.nextTagId();
    const totalTag = tag + '-' + tagId;

    this.callbacks.set(totalTag, callbacks);
    this.worker.postMessage(`(${totalTag} ${message})`);
    return tagId;
  }

  /**
   * Request to serAPI the Abstract Syntax Tree (AST) of a sentence.
   * @param {Number} sentenceNr The number of the sentence
   * @param {Function} onSuccess  What should happen on success
   * @param {Function} onError  What should happen on error
   */
  requestAST(sentenceNr, onSuccess, onError) {
    const msg = `(Query ((sid ${sentenceNr}) (pp ((pp_format PpSer)))) Ast)`;

    const tagId = this.postMessage(msg,
        Constants.AST_COMMAND,
        {onSuccess, onError});
    this.astLog[tagId] = sentenceNr;
  }

  /**
   * Get the next id to use in a message
   *   This method wraps automatically just in case you have a lot of commands
   * @return {number} the id to use
   */
  nextTagId() {
    const value = this.currentMessageNumber;
    this.currentMessageNumber++;
    if (this.currentMessageNumber >= Number.MAX_SAFE_INTEGER - 1) {
      this.currentMessageNumber = 0;
    }
    return value;
  }

  /**
   * Handles messages from SerAPI
   *
   * @param {String} message from SerAPI
   */
  handleMessage(message) {
    if (!this.ready) {
      if (message === Constants.MESSAGE_AFTER_READY) {
        this.ready = true;
        this.onReadyCallback();
      }
      return;
    }

    // TODO: find a better solution to this issue
    let data = message.replace(/ ,\)/g, ' ",")');
    data = data.replace(/'\)/g, ' "\'")');
    const parsedData = parse(data);
    // console.log(data);

    const messageType = parsedData[0];

    // Since feedback is not tagged, we deal with it separately.
    if (messageType === 'Feedback') {
      this.handleFeedback(parsedData);
      return;
    } else if (messageType !== 'Answer') {
      console.warn(`[Warning] Unknown message received ${data}`);
      return;
    }

    const tag = parsedData[1];

    if (!this.callbacks.has(tag)) {
      console.warn(`[Warning] Unknown tag received: ${tag}`);
      return;
    }

    const onSuccess = this.callbacks.get(tag).onSuccess;
    const onErr = this.callbacks.get(tag).onError;

    const respData = parsedData[2];

    if (respData === Constants.MESSAGE_ACK) {
      this.callbackData.set(tag, {_startTime: +new Date()});
      this.currentTag = tag;
    }

    if (respData === Constants.MESSAGE_COMPLETED) {
      this.callbacks.delete(tag);
      if (this.currentTag === tag) {
        this.currentTag = null;
      }
    }

    const storedData = this.callbackData.get(tag);

    switch (this.getResponseType(tag)) {
      case Constants.ADD_COMMAND:
        console.log(message);
        this.handleAddResponse(tag, respData, onSuccess, onErr, storedData);
        break;
      case Constants.AST_COMMAND:
        console.log(message);
        this.handleASTResponse(tag, respData, onSuccess, onErr, storedData);
        break;
      case Constants.CANCEL_COMMAND:
        this.handleCancelResponse(tag, respData, onSuccess, onErr, storedData);
        break;
      case Constants.EXEC_COMMAND:
        this.handleExecuteResponse(tag, respData, onSuccess, onErr, storedData);
        break;
      case Constants.GOAL_COMMAND:
        this.handleGoalsResponse(tag, respData, onSuccess, onErr, storedData);
        break;
      case Constants.SEARCH_COMMAND:
        this.handleSearchResponse(tag, respData, onSuccess);
        break;
    }

    // clear data from this call
    if (respData === Constants.MESSAGE_COMPLETED &&
        this.callbackData.has(tag)) {
      const time = Math.round(
          (+ new Date()) - this.callbackData.get(tag)._startTime) / 1000;
      console.log(`${tag} took ${time}s`);
      this.callbackData.delete(tag);
    }
  }

  /**
   * Extracts the response type from the given tag
   * @param {String} tag The tag to extract the type from
   * @return {String} the name part of the tag
   */
  getResponseType(tag) {
    return tag.split('-', 1)[0];
  }

  /**
   * Handles feedback messages from SerAPI
   * @param {Array} parsedData The contents of the feedback message
   *    as nested arrays
   */
  handleFeedback(parsedData) {
    const feedback = parseFeedback(parsedData);
    if (feedback.string !== '') {
      feedback.string = feedback.string.replace(/ \)/g, ')');
      feedback.string = feedback.string.replace(/\( /g, '(');
      feedback.string = feedback.string.replace(/ ,/g, ',');
      if (feedback.errorFlag === true) {
        feedback.string = 'Error: ' + feedback.string;
      }

      if (this.currentTag) {
        switch (this.getResponseType(this.currentTag)) {
          case Constants.CHECK_COMMAND:
            this.handleCheckFeedback(feedback.string);
            break;
          case Constants.SEARCH_COMMAND:
            // perhaps add colon
            this.handleSearchFeedback(feedback.string);
            break;
          default:
            this.messageCallback(feedback.string);
            break;
        }
      } else {
        this.messageCallback(feedback.string);
      }
    }
  }

  /**
   * Handles feedback messages from SerAPI belonging to a search query
   * @param {string} parsedData The contents of the feedback message,
   *    reduced to a single normal string
   */
  handleSearchFeedback(parsedData) {
    // Ignore results from previous searches
    if (this.currentTag.split('-', 2)[1] !== this.currentSearch + '') {
      return;
    }

    let resultName = parsedData.split(' ', 1)[0];
    // Check gives an error if no object with that exact name exists
    if (resultName === 'Error:') {
      this.searchesCompleted++;
      return;
    }

    if (resultName.endsWith(':')) {
      resultName = resultName.substr(0, resultName.length - 1);
    }

    // Ignore search results that contain a '?'
    if (resultName.indexOf('?') > -1) {
      this.searchesCompleted++;
      return;
    }

    let resultData = parsedData.substring(resultName.length + 1).trim();
    if (resultData[0] === ':') {
      resultData = resultData.substring(1).trim();
    }
    if (!this.searchResults.has(resultName)) {
      const result = {
        name: resultName,
        content: resultData,
        objectName: '',
        isLemma: null,
      };
      this.searchResults.set(resultName, result);
      this.checkType(resultName, resultData);
      this.callbacks.get(this.currentTag).onResult(result);
    }
  }

  /**
   * Handles feedback messages from SerAPI belonging to a check query
   * @param {string} parsedData The contents of the feedback message,
   *    reduced to a single normal string
   */
  handleCheckFeedback(parsedData) {
    const name = this.currentTag.split('-')[1];
    const result = this.searchResults.get(name);

    // Ignore results from previous searches
    if (result === undefined) {
      return;
    }

    this.searchResults.delete(name);

    if (parsedData.trim() === `${result.content} : Prop`) {
      result.objectName = 'Lemma';
      result.isLemma = true;
    } else {
      result.objectName = 'Definition';
      result.isLemma = false;
    }

    if (this.searchResults.size === 0) {
      this.callbacks.get(this.currentTag).onSuccess();
    }
  }

  /**
   * Handles an AST response from SerAPI
   * @param {String} tag The tag associated with the AST request
   * @param {Array} response Nested array
   * @param {Function} onSuccess Callback function if everything is ok
   * @param {Function} onError Callback function if error occurred
   * @param {Array} data So far seems not used
   */
  handleASTResponse(tag, response, onSuccess, onError, data) {
    // TODO: error handling
    if (response === Constants.MESSAGE_ACK) {
      data.exceptionOccurred= false;
      data.ast = null;
    } else if (response === Constants.MESSAGE_COMPLETED) {
      if (!data.exceptionOccurred) {
        const tagId = tag.split('-', 2)[1];
        onSuccess({
          sentenceId: this.astLog[tagId],
          sentenceAST: data.ast,
        });
        // Clean up from dictionary
        delete this.astLog[tagId];
      } else {
        onError();
      }
    } else { // TODO: change to appropriate message characteristic
      data.ast = extractAST(response);
    }
  }

  /**
    * Handles response for add
    *
    * @param {string} tag The tag associated with the execution
    * @param {array|String} response The response in the response
    * @param {Function} onSuccess The callback for success
    * @param {Function} onError The callback for errors
    * @param {object} data the data of the response
    */
  handleAddResponse(tag, response, onSuccess, onError, data) {
    if (response === Constants.MESSAGE_ACK) {
      data.exceptionOccurred= false;
      data.sentences = [];
    } else if (response === Constants.MESSAGE_COMPLETED) {
      if (!data.exceptionOccurred) {
        onSuccess(data.sentences);
      } else {
        onSuccess(data.sentences);
        onError(data.exception);
      }
    } else if (!Array.isArray(response)) {
      throw new Error('Response for tag ' + tag + ' was not an array');
    } else if (response[0] === 'Added') {
      const sid = +response[1];
      const options = flatten(response[2]);
      const tagId = tag.split('-', 2)[1];
      // TODO: the solution with the if statement below is
      // just to make the test work...
      let sentenceString = '';
      let bp = options.bp;
      let ep = options.ep;
      const str = this.addLog[tagId];
      if ( str ) {
        bp = byteIndexToStringIndex(str, options.bp);
        ep = byteIndexToStringIndex(str, options.ep);
        sentenceString = str.slice(bp, ep);
        // TODO: clear up addLog dictionary
      }
      data.sentences.push({
        sentenceId: sid,
        beginIndex: +bp,
        endIndex: +ep,
        sentence: sentenceString,
      });
    } else {
      if (response[0] === Constants.COQ_EXCEPTION) {
        data.exceptionOccurred = true;
        data.exception = parseErrorResponse(response);
      }
    }
  }

  /**
   * Handles response for cancel
   *
   * @param {string} tag The tag associated with the execution
   * @param {Array|String} response The response in the response
   * @param {Function} onSuccess The callback for success
   * @param {Function} onError The callback for errors
   * @param {object} data the data of the response
   */
  handleCancelResponse(tag, response, onSuccess, onError, data) {
    if (response === Constants.MESSAGE_ACK) {
      data.exceptionOccurred = false;
      data.removedSentences = [];
    } else if (response === Constants.MESSAGE_COMPLETED) {
      if (!data.exceptionOccurred) {
        onSuccess(data.removedSentences);
      } else {
        onError(data.exception);
      }
    } else if (response[0] === 'Canceled') {
      data.removedSentences = data.removedSentences.concat(
          response[1].map(Number));
    }
  }

  /**
   * Handles response for executions
   *
   * @param {string} tag The tag associated with the execution
   * @param {Array|String} response The response in the response
   * @param {Function} onSuccess The callback for success
   * @param {Function} onError The callback for errors
   * @param {object} data the data of the response
   */
  handleExecuteResponse(tag, response, onSuccess, onError, data) {
    if (response === Constants.MESSAGE_COMPLETED && !data.exceptionOccurred) {
      onSuccess();
    }
    if (response[0] === Constants.COQ_EXCEPTION) {
      data.exceptionOccurred = true;
      onError(parseErrorResponse(response));
    }
  }

  /**
   * Handles responses from the getGoals function: calls the correct callback
   * for each response (except Ack/Completed), and deletes the callback on
   * Completed.
   *
   * @param {string} tag the tag the answers start with, indicating which
   *                     set of callbacks should be used
   * @param {Array|String} response the response associated with the response,
   *   parsed from s-expression to nested arrays
   * @param {Function} onSuccess The callback for success
   * @param {Function} onError The callback for errors
   * @param {object} data the data of the response
   */
  handleGoalsResponse(tag, response, onSuccess, onError, data) {
    if (response === Constants.MESSAGE_ACK) {
      data.completed = false;
      return;
    } else if (response === Constants.MESSAGE_COMPLETED) {
      if (!data.completed) {
        onError('Could not read/parse goals');
      } else {
        onSuccess(data.goal);
      }
      return;
    }

    if (response[0] === 'ObjList') {
      data.completed = true;

      if (!Array.isArray(response[1])) {
        return;
      }

      if (response[1].length < 1) {
        data.goal = '';
        return;
      }

      // TODO, mooier als het kan
      const objectives = response[1][0];

      if (objectives === []) {
        data.goal = '';
        // no goals
        return;
      }

      if (objectives[0] === 'CoqString') {
        data.goal = objectives[1].toString();
      }
    }
  }

  /**
   * Handles responses from the search functions
   *
   * @param {string} tag The tag associated with the search
   * @param {string} response The type of the response
   * @param {Function} onSuccess The function to call when searching is done
   */
  handleSearchResponse(tag, response, onSuccess) {
    if (response === Constants.MESSAGE_COMPLETED
        || response === Constants.COQ_EXCEPTION) {
      if (tag.split('-', 2)[1] == this.currentSearch) {
        this.searchesCompleted++;
        if (this.searchResults.size === 0 && this.searchesCompleted === 3) {
          onSuccess();
        }
      }
    }
  }

  /**
   * Whether this serapi interface is ready to send commands
   *
   * @return {Boolean} true when ready
   */
  isReady() {
    return this.ready;
  }

  /**
   * Stop this instance of coq
   */
  terminate() {
    this.worker.terminate();
  }
}

export default SerapiCommands;
