const flatten = require('./flatten-expr').flatten;

// constants
const MESSAGE_COMPLETED = 'Completed';
const MESSAGE_ACK = 'Ack';
const COQ_EXCEPTION = 'CoqExn';

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
 * Parse feedback which could contain an error
 * @param {*} data the feedback
 * @return {{string: string, errorFlag: boolean}} the text in the feedback
 *   with errorflag set if true
 */
function parseErrorableFeedback(data) {
  const feedback = parseFeedback(data);
  if (feedback.string === '') {
    return feedback;
  }
  feedback.string = feedback.string
      .replace(/ \)/g, ')')
      .replace(/\( /g, '(')
      .replace(/ ,/g, ',');
  if (feedback.errorFlag === true) {
    feedback.string = 'Error: ' + feedback.string;
  }
  return feedback;
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
  // TODO: fix that it sometimes gives: ' , bla bla'
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


  const flatResponse = flatten(response);

  if (flatResponse.length < 2) {
    return {
      lastCorrectSentence: lastSentenceIdCorrect,
      failureAtSentence: failureSentenceId,
      beginIndex: bp,
      endIndex: ep,
      message: message,
    };
  }

  if (flatResponse[0] !== COQ_EXCEPTION) {
    console.log('Warning might not be an error');
  }

  const responseContent = flatResponse[1];

  if (responseContent.hasOwnProperty('loc')) {
    bp = +responseContent.loc.bp;
    ep = +responseContent.loc.ep;
  }

  if (responseContent.hasOwnProperty('stm_ids')) {
    if (Array.isArray(responseContent.stm_ids)
          && responseContent.stm_ids.length > 0) {
      const stms = responseContent.stm_ids[0];
      lastSentenceIdCorrect = +stms[0];
      failureSentenceId = +stms[1];
    }
  }

  if (responseContent.hasOwnProperty('str')) {
    message = responseContent.str;
  }

  if (responseContent.hasOwnProperty('exn')) {
    message += '(' + responseContent.exn.join(',') + ')';
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

/**
 * Parse goals from serapi message
 * @param {*} response the serapi message
 * @return {string|*} the resulting goal
 */
function getGoalsFromResponse(response) {
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

/**
 * Checks whether a given message is acknowledge or complete (a general message)
 * @param {*} response the serapi message
 * @return {boolean} whether it is a general message
 */
function isGeneralMessage(response) {
  return response === MESSAGE_ACK ||
      response === MESSAGE_COMPLETED;
}

/**
 * Parse Add output to a sentence
 * @param {*} response the serapi message
 * @return {{endIndex: *, beginIndex: *, sentenceId: *}|null} the resulting
 *   sentence
 */
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

/**
 * Check if the response is (a general) ready feedback message
 * @param {*} response the response to check
 * @return {boolean} whether it is the ready responds
 */
function isReadyFeedback(response) {
  // this is not great... but there is nothing really unique about so it will
  // suffice
  return response[0] === 'Feedback'
      && response[1].length === 4
      && response[1][3].length === 2
      && response[1][3][0] === 'contents'
      && response[1][3][1] === 'Processed';
}

/**
 * For a given string, convert an index in terms of bytes (as often
 * provided by serapi) to an index in terms of a string
 * @param {String} str The string to perform the conversion for
 * @param {Number} byteIndex The index in terms of bytes
 * @return {Number} The index in the string corresponding to the
 * given byte, or -1 if it cannot be found
 */
function byteIndexToStringIndex(str, byteIndex) {
  for (let j = Math.floor(byteIndex / 2); j <= byteIndex; j++) {
    if (Buffer.byteLength(str.slice(0, j)) === byteIndex) {
      return j;
    }
  }
  return -1;
}

/**
 * For a given string, compute a conversion from byte indices
 * to string indices
 * @param {String} str The string to compute the conversion for
 * @return {Array} An array a such that a[i] is the index in the string
 * of the character with byte index i
 */
function byteIndicesToStringIndices(str) {
  const conversion = [];

  for (let i = 0; i < str.length; i++ ) {
    for (let j = 0; j < Buffer.byteLength(str[i]); j++ ) {
      conversion.push(i);
    }
  }
  return conversion;
}

export {
  parseFeedback, parseErrorableFeedback, parseErrorResponse,
  sanitise, getLastValidFullStop, isReadyFeedback,
  getGoalsFromResponse, isGeneralMessage, parseToSentence,
  byteIndexToStringIndex, byteIndicesToStringIndices,
  COQ_EXCEPTION, MESSAGE_ACK, MESSAGE_COMPLETED,
};
