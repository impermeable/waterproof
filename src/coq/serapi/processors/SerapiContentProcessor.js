import SerapiProcessor from '../util/SerapiProcessor';
import {
  byteIndicesToStringIndices,
  COQ_EXCEPTION,
  getGoalsFromResponse,
  detectUnfocusedGoal,
  getLastValidFullStop,
  parseErrorResponse,
  parseToSentence,
} from '../SerapiParser';
import {Mutex} from 'async-mutex';
import {
  createAddCommand,
  createCancelCommand,
  createGoalCommand,
} from '../util/SerapiCommandFactory';

/**
 * Processor for content
 * Add, cancels and get the goal after modification of content
 */
class SerapiContentProcessor extends SerapiProcessor {
  /**
   * Create a SerapiContentProcessor
   * @param {SerapiTagger} tagger the tagger to use
   * @param {SerapiState} state the state to use
   * @param {EditorInterface} editor the editor to use
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
    this.currentContent = '';
    this.addLock = new Mutex();

    this.contentLock = new Mutex();


    this.addContent = '';
  }

  /**
   * Sets the Coq content to the given string.
   * @param {string} content The Coq code to set the content to.
   */
  async setContent(content) {
    const releaseNewContent = await this.addLock.acquire();

    this.addContent = content;

    if (this.contentLock.isLocked()) {
      releaseNewContent();
      return Promise.resolve();
    }


    const releaseContentLock = await this.contentLock.acquire();
    const stateRelease = await this.state.stateLock.acquire();

    let newContent = this.addContent;
    releaseNewContent();

    while (this.currentContent !== newContent) {
      const lastUnchangedSentence = this._getLastUnchangedSentence(newContent);

      // either everything or from the last sentence
      const editIndex = lastUnchangedSentence === -1 ? -1 :
          this.state.endIndexOfSentence(lastUnchangedSentence);
      const contentToAdd = lastUnchangedSentence === -1 ? newContent :
          newContent.slice(editIndex);

      if (this.state.lastExecuted > lastUnchangedSentence) {
        // FIRST revert the goal since it is visible to the user
        await this._getRerolledGoal(lastUnchangedSentence, editIndex);
      }

      const sentencesToCancel = [];
      for (let i = lastUnchangedSentence + 1;
        i < this.state.sentenceSize(); i++) {
        sentencesToCancel.push(this.state.idOfSentence(i));
      }

      if (sentencesToCancel.length > 0) {
        // SECOND cancel any needed sentences
        await this._cancelSentences(sentencesToCancel);
      }

      if (lastUnchangedSentence === -1) {
        this.currentContent = '';
      } else {
        this.currentContent = this.currentContent.slice(0, editIndex);
      }

      // AND FINALY set the actual new content
      await this._setNewContent(contentToAdd);
      newContent = await this._getCurrentNewContent();
    }

    // update target in case it is too large
    this.state.target = Math.min(
        this.state.target, this.state.sentenceSize() - 1);
    stateRelease();
    releaseContentLock();
    return Promise.resolve();
  }

  /**
   * Get new content (with lock)
   * @private
   */
  async _getCurrentNewContent() {
    const release = await this.addLock.acquire();
    const newContentValue = this.addContent + '';
    release();
    return newContentValue;
  }

  /**
   * Get goal from serapi if rerolling
   * @param {Number} lastUnchangedSentence the sentence index of the last valid
   *   sentence
   * @param {Number} editIndex the index where the first edit was made
   * @private
   */
  async _getRerolledGoal(lastUnchangedSentence, editIndex) {
    let newGoal = '';
    if (lastUnchangedSentence >= 0) {
      const sentenceId = this.state.idOfSentence(lastUnchangedSentence);
      const baseGoal = await this.sendCommand(
          createGoalCommand(sentenceId), 'g');
      let goalString = baseGoal.goal;
      if (baseGoal.goal === '') {
        const serapiGoal = await this.sendCommand(
            createGoalCommand(sentenceId.toString(), 'PpSer'), 'k');
        if (serapiGoal.next_goal_message != null) {
          goalString += '\n';
          goalString += serapiGoal.next_goal_message;
        }
      }
      newGoal = goalString;
    }

    this.state.lastExecuted = lastUnchangedSentence;
    this.state.target = Math.min(this.state.target, lastUnchangedSentence);
    this.editor.executeStarted(lastUnchangedSentence < 0 ? -1
        : this.state.endIndexOfSentence(lastUnchangedSentence));
    this.editor.setContentSuccess(newGoal, editIndex, true);
  }

  /**
   * Send a cancel command
   * @param {*} sentences sentences to cancel
   * @private
   */
  async _cancelSentences(sentences) {
    return this.sendCommand(createCancelCommand(sentences), 'c');
  }

  /**
   * Sanitize and validate new content and send command to set it
   * @param {String} contentToAdd the new command
   * @return {Promise<void>}
   * @private
   */
  async _setNewContent(contentToAdd) {
    const validatedContent = this._toValidContent(contentToAdd);
    if (validatedContent !== '') {
      return this.sendCommand(createAddCommand(validatedContent), 'a')
          .then((result) => this._processSentences(result, contentToAdd));
    } else {
      this.editor.setContentSuccess(null, -1, true);
      this.currentContent += contentToAdd;
      return Promise.resolve();
    }
  }

  /**
   * Process results of add commands
   * @param {*} result the sentence
   * @param {String} contentAdded the text content which was added
   * @private
   */
  _processSentences(result, contentAdded) {
    const baseOffset = this.currentContent.length;
    let furthestIndex = -1;
    const sentences = [];
    const conversion = byteIndicesToStringIndices(contentAdded);
    for (const [key, value] of Object.entries(result)) {
      if (key !== 'error') {
        const bp = conversion[value.beginIndex];
        const ep = conversion[value.endIndex];
        const stringValue = contentAdded.slice(bp, ep);
        sentences.push({sid: value.sentenceId, str: stringValue,
          bp: bp + baseOffset, ep: ep + baseOffset,
        });
        furthestIndex = Math.max(furthestIndex, ep);
      }
    }

    for (const sentence of sentences.sort((a, b) => a.sid - b.sid)) {
      this.state.addSentence(sentence.sid,
          sentence.bp, sentence.ep, sentence.str);
    }

    if (result.hasOwnProperty('error')) {
      this.currentContent += contentAdded;

      if (furthestIndex > -1) {
        this.editor.setContentSuccess(null, -1, true);
      }
      this.editor.setContentError(result.error);
    } else {
      // no error
      this.currentContent += contentAdded;
      this.editor.setContentSuccess(null, -1, true);
    }
  }

  /**
   * Check if sentence ends in . or *)
   * @param {String} contentToAdd the content to check
   * @return {String} the valid content to add
   * @private
   */
  _toValidContent(contentToAdd) {
    const trimmed = contentToAdd.trim();
    if (trimmed === '') {
      return trimmed;
    }

    if (!(trimmed.endsWith('.') || trimmed.endsWith('*)') )) {
      let validSentenceIndex = getLastValidFullStop(contentToAdd + ' ');
      if (validSentenceIndex < 0) {
        validSentenceIndex = getLastValidFullStop(this.currentContent + ' ');
        contentToAdd = '';
      } else {
        contentToAdd = contentToAdd.slice(0, validSentenceIndex + 1);
        validSentenceIndex += this.currentContent.length;
      }

      this.editor.setContentError(
          'Sentence not closed (did you forget a "." or "*)" ?)',
          validSentenceIndex);
    }
    return contentToAdd;
  }

  /**
   * Calculate the last still valid sentence when using other content
   * @param {String} otherContent the content to check with
   * @return {Number} the index of the last valid sentence
   * @private
   */
  _getLastUnchangedSentence(otherContent) {
    const firstDifference = this._getDifferenceIndex(otherContent);
    if (firstDifference >= otherContent.length ||
        /\s/.test(otherContent[firstDifference])) {
      // The first changed character is whitespace
      return this.state.sentenceBeforeIndex(firstDifference);
    } else {
      // The first changed character is not whitespace
      return this.state.sentenceBeforeIndex(firstDifference - 1);
    }
  }

  /**
   * Find the first difference index between two string
   * @param {String} otherContent the content to compare to
   * @return {number} the index of the first difference
   * @private
   */
  _getDifferenceIndex(otherContent) {
    const minLength = Math.min(this.currentContent.length, otherContent.length);
    if (minLength === 0) {
      return -1;
    }
    for (let i = 0; i < minLength; i++) {
      if (this.currentContent[i] !== otherContent[i]) {
        return i;
      }
    }
    return minLength;
  }

  /**
   * Handle a serapi message
   * @param {*} data the serapi message (parsed)
   * @param {String} extraTag the extra identifying tag
   * @return {*} partial of this command
   */
  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'c') {
      if (Array.isArray(data) && data[0] === 'Canceled') {
        for (const sid of data[1].map(Number)) {
          this.state.removeSentence(sid);
        }
      }
    } else if (extraTag === 'k') {
      return detectUnfocusedGoal(data);
    } else if (extraTag === 'g') {
      // rerolled goal
      return {
        goal: getGoalsFromResponse(data),
      };
    } else if (extraTag === 'a') {
      if (data[0] === COQ_EXCEPTION) {
        return {
          error: parseErrorResponse(data),
        };
      }
      // update offset?
      const sentence = parseToSentence(data);
      return {
        [sentence.sentenceId]: sentence,
      };
    } else {
      console.log('Unknown extra tag in SerapiContentProcessor');
    }
  }
}

export default SerapiContentProcessor;
