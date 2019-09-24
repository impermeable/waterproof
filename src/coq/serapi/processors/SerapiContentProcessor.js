import SerapiProcessor from '../util/SerapiProcessor';
import {
  getGoalsFromResponse, getLastValidFullStop,
  isGeneralMessage, parseErrorResponse, parseToSentence,
} from '../SerapiParser';
import * as Constants from '../SerapiConstants';
import {byteIndexToStringIndex} from '../StringIndices';
import {Mutex} from 'async-mutex';
import {
  createAddCommand, createCancelCommand, createGoalCommand,
} from '../util/SerapiCommandFactory';

class SerapiContentProcessor extends SerapiProcessor {
  /**
   *
   * @param {SerapiTagger} tagger
   * @param {SerapiState} state
   * @param {EditorInterface} editor
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
    this.currentContent = '';
    this.addLock = new Mutex();

    this.contentLock = new Mutex();


    this.addContent = '';
  }

  async setContent(content) {
    const releaseNewContent = await this.addLock.acquire();

    this.addContent = content;

    if (this.contentLock.isLocked()) {
      releaseNewContent();
      // TODO: what is the best way to return promises?
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

      if (editIndex !== -1 && this.state.lastExecuted > lastUnchangedSentence) {
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

  async _getCurrentNewContent() {
    const release = await this.addLock.acquire();
    const newContentValue = this.addContent + '';
    release();
    return newContentValue;
  }

  async _getRerolledGoal(lastUnchangedSentence, editIndex) {
    if (lastUnchangedSentence < 0) {
      // reroll everything
      this.editor.setContentSuccess('', editIndex, true);
      return Promise.resolve();
    }
    const sentenceId = this.state.idOfSentence(lastUnchangedSentence);
    return this.sendCommand(createGoalCommand(sentenceId), 'g')
        .then((result) => {
          this.state.lastExecuted = lastUnchangedSentence;
          this.editor.setContentSuccess(result.goal, editIndex, true);
        });
  }

  // TODO: move command creation to separate file
  async _cancelSentences(sentences) {
    return this.sendCommand(createCancelCommand(sentences), 'c');
  }

  async _setNewContent(contentToAdd) {
    const validatedContent = this._toValidContent(contentToAdd);
    if (validatedContent !== '') {
      return this.sendCommand(createAddCommand(validatedContent), 'a')
          .then((result) => this._processSentences(result, validatedContent));
    } else {
      this.editor.setContentSuccess(null, -1, true);
      return Promise.resolve();
    }
  }

  _processSentences(result, contentAdded) {
    const baseOffset = this.currentContent.length;
    let furthestIndex = -1;
    for (const [key, value] of Object.entries(result)) {
      // TODO: need to check for order!!
      if (key !== 'error') {
        const bp = byteIndexToStringIndex(contentAdded, value.beginIndex);
        const ep = byteIndexToStringIndex(contentAdded, value.endIndex);
        const stringValue = contentAdded.slice(bp, ep);
        this.state.addSentence(value.sentenceId,
            bp + baseOffset, ep + baseOffset, stringValue);
        furthestIndex = Math.max(furthestIndex, ep);
      }
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

  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'c') {
      if (Array.isArray(data) && data[0] === 'Canceled') {
        for (const sid of data[1].map(Number)) {
          this.state.removeSentence(sid);
        }
      }
    } else if (extraTag === 'g') {
      // rerolled goal
      if (!isGeneralMessage(data)) {
        return {
          goal: getGoalsFromResponse(data),
        };
      }
    } else if (extraTag === 'a') {
      if (!isGeneralMessage(data)) {
        if (data[0] === Constants.COQ_EXCEPTION) {
          return {
            error: parseErrorResponse(data),
          };
        }
        // update offset?
        const sentence = parseToSentence(data);
        return {
          [sentence.sentenceId]: sentence,
        };
      }
    } else {
      console.log('Unknown extra tag in SerapiContentProcessor');
    }
  }

  handleSerapiFeedback(feedback, extraTag) {
  }
}

export default SerapiContentProcessor;
