const flatten = require('./flatten-expr').flatten;
import * as Constants from './SerapiConstants';

/**
 * Function to handle feedback message received from SerAPI
 *
 * @param {Array} data array of parsed data representing the message
 * @return {Object} the segments of the data preceded by "CoqString"
 */
function parseFeedback(data) {
  // TODO fix spaces by recognizing Pp_glue and stuff
  const feedback = {
    string: '',
    errorFlag: false,
  };
  if (data[1] === 'Error') {
    feedback.errorFlag = true;
  }
  if (data[0] === 'Pp_string') {
    if (data[1].trim() !== '') {
      feedback.string = data[1].trim() + ' ';
    }
    return feedback;
  } else {
    if (Array.isArray(data)) {
      for (const cell of data) {
        const obj = parseFeedback(cell);
        feedback.string += obj.string;
        feedback.errorFlag = (feedback.errorFlag || obj.errorFlag);
      }
      feedback.string = feedback.string.replace(/ \. /g, '.');
      return feedback;
    }
  }
  return feedback;
}

/**
 * Try to get just the informative parts of a serapi recursive message
 * @param {Object|string|Array} response the response
 * @return {string} the parsed answer
 */
function parseRecursiveMessage(response) {
  if (!Array.isArray(response)) {
    return '';
  }
  if (response.length > 2) {
    return parseRecursiveMessage(response[2]);
  } else {
    // only give the root cause (since it is usually the most descriptive one)
    return response[1] + '';
  }
}

/**
 * Parse a CoqExn from serapi
 * This method *should* be safe e.g. not crash and will try to extract as
 * much information as possible
 * @param {Array} response the parsed response in which the error occurs
 * @return {Object} the error with:
 *  message: String,
 *  beginIndex: begin index,
 *  endIndex: end index,
 *  lastCorrectSentence: the sentence id which was still correct
 *  failureAtSentence: the sentence id at which the error occurred (can be 0)
 */
function parseErrorResponse(response) {
  let bp = -1;
  let ep = -1;
  let lastSentenceIdCorrect = -1;
  let failureSentenceId = -1;
  let message = 'Unknown error occurred';

  if (!Array.isArray(response)) {
    return {
      lastCorrectSentence: lastSentenceIdCorrect,
      failureAtSentence: failureSentenceId,
      beginIndex: bp,
      endIndex: ep,
      message: message,
    };
  }

  if (response[0] !== Constants.COQ_EXCEPTION) {
    console.log('Warning might not be an error');
  }

  if (response.length > 1 && Array.isArray(response[1]) &&
      response[1].length > 0) {
    if (Array.isArray(response[1][0])) {
      const locations = flatten(response[1][0]);
      bp = locations.bp;
      ep = locations.ep;
    } else {
      console.log('unknown locations:');
      console.log(response[1]);
      console.warn(response[1]);
    }
  }

  if (response.length > 2) {
    const sentenceOffset = response[2][0];
    if (Array.isArray(sentenceOffset) && sentenceOffset.length > 1) {
      lastSentenceIdCorrect = +sentenceOffset[0];
      failureSentenceId = +sentenceOffset[1];
    }
  }

  if (response.length > 3) {
    if (!Array.isArray(response[3]) ||
        response[3][0] !== 'Backtrace' ||
        !Array.isArray(response[3][1]) ||
        response[3][1].length > 0) {
      console.log('Non backtrace please investigate:');
      console.log(response[3]);
      console.warn(response[3]);
      console.error(response[3]);
      console.info(response[3]);
    }
  }

  if (response.length > 4) {
    const responseMessage = response[4];
    if (!Array.isArray(responseMessage)) {
      message = responseMessage;
    } else {
      message = parseRecursiveMessage(response[4]);
    }
  }

  return {
    lastCorrectSentence: lastSentenceIdCorrect,
    failureAtSentence: failureSentenceId,
    beginIndex: bp,
    endIndex: ep,
    message: message,
  };
}

/**
 * Escapes double quotes and slashes in a string
 *
 * @param {string} str the string to be sanitised
 * @return {string} the sanitised string
 */
function sanitise(str) {
  return str.replace(/\\/g, '\\\\')
      .replace(/"/g, '\\"');
}


/**
 * Calculate where the last stop of coq code is
 * @param {String} text the text to search in
 * @return {number} the index of the last valid stop
 */
function getLastValidFullStop(text) {
  const pattern = /\.\s/g;
  let lastMatch = false;
  let match;

  while ((match = pattern.exec(text)) !== null) {
    lastMatch = match;
  }

  if (lastMatch) {
    return lastMatch.index;
  } else {
    return -1;
  }
}

function getGoalsFromResponse(response) {
  if (isGeneralMessage(response)) {
    return false;
  }

  if (response[0] === 'ObjList') {
    if (!Array.isArray(response[1]) || response[1].length < 1) {
      return '';
    }

    const objectives = response[1][0];

    if (objectives === []) {
      return '';
    }

    if (objectives[0] === 'CoqString') {
      return objectives[1].toString();
    }
  }
  return '';
}

function isGeneralMessage(response) {
  return response === Constants.MESSAGE_ACK ||
      response === Constants.MESSAGE_COMPLETED;
}

function parseToSentence(response) {
  if (response[0] !== 'Added') {
    return null;
  }
  const sid = +response[1];
  const options = flatten(response[2]);
  return {
    sentenceId: sid,
    beginIndex: options.bp,
    endIndex: options.ep,
  };
}

export {
  parseFeedback, parseErrorResponse, sanitise, getLastValidFullStop,
  getGoalsFromResponse, isGeneralMessage, parseToSentence,
};

