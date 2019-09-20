'use strict';

import {Mutex} from 'async-mutex';
import CoqInterface from '../CoqInterface';
import SerapiSentences from './SerapiSentences';
import {getLastValidFullStop} from './SerapiParser';

/**
 * The main interface to SerAPI. Exposes a JavaScript interface where commands
 * are sent with onSuccess and onError handlers, one of which will be called
 * when SerAPI's responses to the command come in.
 */
class CoqSerapi extends CoqInterface {
  /**
   * Creates a new CoqInterface from the specified or default
   *  worker location.
   * @param {SerapiInterface} serapi the interface for serapi
   * @param {EditorInterface} editor the editor to send back to
   */
  constructor(serapi, editor) {
    super();
    this.serapiImpl = serapi;
    this.editorImpl = editor;
    this.sentences = new SerapiSentences();

    this.currentContent = '';

    this.newContent = '';
    this.addLock = new Mutex();
    this.newContentLock = new Mutex();

    this.addUnlock = null;

    this.addNumber = 0;

    this.targetLock = new Mutex();
    this.executeTarget = {index: -1, offset: 0};

    this.lastExecuted = -1;
    this.executeLock = new Mutex();

    this.validate = () => {};
  }

  /**
   * Sets the Coq content to the given string.
   *
   * @param {string} content The Coq code to set the content to.
  */
  async setContent(content) {
    if (!this.serapiImpl.isReady()) {
      // Wait until serapi is ready to receive input
      return;
    }

    const releaseNewContent = await this.newContentLock.acquire();

    if (this.addLock.isLocked()) {
      console.log('Storing newContent');
      // someone else is running
      this.newContent = content;
      releaseNewContent();
      return;
    }

    const releaseAddLock = await this.addLock.acquire();

    clearTimeout(this.addUnlock);

    const addNum = ++this.addNumber;

    this.addUnlock = setTimeout(() => {
      if (this.addLock.isLocked() && this.addNumber === addNum) {
        console.log('emergency unlock of add');
        releaseAddLock();
      }
    }, 3000);

    releaseNewContent();
    // this function should be called before any return, or after any onError
    // or onSuccess e.g. and then release the addLock

    const checkNewContent = async () => {
      const releaseNewContent = await this.newContentLock.acquire();
      const releaseTarget = await this.targetLock.acquire();
      const newContent = this.newContent;
      this.newContent = '';
      let execute = false;
      if (this.executeTarget.offset !== 0 || this.executeTarget.index >= 0) {
        execute = true;
      }
      releaseTarget();
      releaseAddLock();
      releaseNewContent();
      if (newContent !== '') {
        this.setContent(newContent);
        // restart adding content
      } else if (execute) {
        // if execution needs to take place this will handle it
        this.executeToTarget();
      }
    };

    const lastUnchangedSentence = this.getLastUnchangedSentence(content);

    let toAdd;
    let editIndex = -1;
    if (lastUnchangedSentence === -1) {
      // No unchanged sentences, everything should be added again
      toAdd = content;
    } else {
      editIndex = this.sentences.endIndex(lastUnchangedSentence);
      toAdd = content.slice(editIndex);
    }

    const releaseTarget = await this.targetLock.acquire();

    let sentenceTarget = this.targetToSentenceIndex();
    if (sentenceTarget !== this.lastExecuted && sentenceTarget >= 0) {
      this.executeTarget.index = -1;

      if (sentenceTarget > lastUnchangedSentence) {
        sentenceTarget = lastUnchangedSentence;
      }

      this.executeTarget.offset = sentenceTarget - this.lastExecuted;
      this.editorImpl.executeStarted(this.sentences.endIndex(sentenceTarget));
    }

    releaseTarget();

    const sentenceIdsToCancel = [];
    for (let i = lastUnchangedSentence+1; i < this.sentences.length(); i++) {
      sentenceIdsToCancel.push(this.sentences.id(i));
    }

    if (sentenceIdsToCancel.length > 0) {
      // If there are sentences to be removed, then call the cancel function
      this.serapiImpl.cancel(sentenceIdsToCancel,
          (removedSentences) => {
            this.setContentAfterCancel(lastUnchangedSentence, toAdd,
                checkNewContent);
          }, this.editorImpl.setContentError);
    } else {
      // Otherwise immediately call setContentAfterCancel to continue
      this.setContentAfterCancel(lastUnchangedSentence, toAdd, checkNewContent);
    }
  }

  /**
   * Returns the index in the sentences array of the last unchanged sentence
   * If this end coincides with the end of the content, then return the previous
   * index to correctly handle triple periods
   *
   * @param {string} newContent
   * @return {number} The index of the last unchanged sentence in sentences
   */
  getLastUnchangedSentence(newContent) {
    let unchangedIndex = -1;
    while (unchangedIndex+1 < this.currentContent.length &&
        unchangedIndex+1 < newContent.length &&
        this.currentContent[unchangedIndex+1] ===
          newContent[unchangedIndex+1]) {
      unchangedIndex++;
    }
    if (unchangedIndex+1 >= newContent.length ||
        /\s/.test(newContent[unchangedIndex+1])) {
      // The first changed character is whitespace
      return this.sentences.sentenceBeforeIndex(unchangedIndex+1);
    } else {
      // The first changed character is not whitespace
      return this.sentences.sentenceBeforeIndex(unchangedIndex);
    }
  }

  /**
   * The part of the setContent function that should be executed after\
   * successful canceling of the changed sentences
   *
   * @param {number} lastUnchangedSentence The index in the sentences
   *    array of the last unchanged sentence
   * @param {string} toAdd The part of the content that needs to be added
   * @param {Function} checkNewContent the function to call after completion
   */
  setContentAfterCancel(lastUnchangedSentence, toAdd, checkNewContent) {
    if (lastUnchangedSentence === -1) {
      this.currentContent = '';
    } else {
      this.currentContent = this.currentContent.slice(0,
          this.sentences.endIndex(lastUnchangedSentence));
    }
    this.sentences.removeAfter(lastUnchangedSentence + 1);

    // Rollback if something is changed before the execution point
    let executionPointChanged;
    if (this.lastExecuted > lastUnchangedSentence) {
      this.lastExecuted = lastUnchangedSentence;
      executionPointChanged = true;
    } else {
      executionPointChanged = false;
    }

    // Skip empty content
    const trimmed = toAdd.trim();
    if (trimmed === '') {
      this.getGoalsLastExecuted(executionPointChanged, false);
      checkNewContent();
      return;
    }

    // If the stuff to add is definitely invalid, quit

    let errorOccured = false;
    // TODO check if still in comment, is also a valid end
    // note probably just use a regex
    if (!(trimmed.endsWith('.') || trimmed.endsWith('*)') )) {
      let validSentenceIndex = getLastValidFullStop(toAdd + ' ');
      if (validSentenceIndex < 0) {
        validSentenceIndex = getLastValidFullStop(this.currentContent + ' ');
        toAdd = '';
      } else {
        toAdd = toAdd.slice(0, validSentenceIndex+1);
        validSentenceIndex += this.currentContent.length;
      }

      this.editorImpl.setContentError(
          'Sentence not closed (did you forget a "." or "*)" ?)',
          validSentenceIndex);
      errorOccured = true;

      // Skip empty content
      if (toAdd.trim() === '') {
        this.getGoalsLastExecuted(executionPointChanged, false);
        checkNewContent();
        return;
      }
    }

    this.serapiImpl.add(toAdd, (addedSentences) => {
      // Adjust the indices of the addedSentences to account for
      // the text added earlier.
      const indexOffset = this.currentContent.length;
      for (let i = 0; i < addedSentences.length; i++) {
        addedSentences[i].beginIndex += indexOffset;
        addedSentences[i].endIndex += indexOffset;
        addedSentences[i].startOffset = indexOffset;
        this.getAST(addedSentences[i].sentenceId);
      }
      this.currentContent += toAdd;
      this.sentences.concat(addedSentences);

      this.getGoalsLastExecuted(executionPointChanged, !errorOccured);
      checkNewContent();
    }, (error) => {
      this.editorImpl.setContentError(error.message, error.beginIndex);
      checkNewContent();
    });
  }

  /**
   * Gets the goals and corresponding index at this.lastExecuted,
   * or null for the goals when executionPointChanged is false.
   *
   * @param {boolean} executionPointChanged boolean to indicate whether
   * @param {boolean} removeAddError  Whether the addError should be removed
   */
  getGoalsLastExecuted(executionPointChanged, removeAddError) {
    if (this.lastExecuted === -1) {
      // No executed code
      this.editorImpl.setContentSuccess('', -1, removeAddError);
    } else if (executionPointChanged) {
      // The goals changed
      this.getGoalsAtSentence(this.lastExecuted, (goal) => {
        const endIndex = this.sentences.endIndex(this.lastExecuted);
        this.editorImpl.setContentSuccess(goal, endIndex, removeAddError);
      }, this.editorImpl.setContentError);
    } else {
      // No changes in goals
      this.editorImpl.setContentSuccess(null,
          this.sentences.endIndex(this.lastExecuted), removeAddError);
    }
  }

  /**
   * Executes the next Coq sentence
   */
  async executeNext() {
    return this.executeOffset(+1);
  }

  /**
   * Rollback to the previous Coq sentence
   */
  async executePrevious() {
    return this.executeOffset(-1);
  }

  /**
   * Execute a number of sentences from the current position
   * @param {Number} offset how many to execute
   * @return {Promise<*>}
   */
  async executeOffset(offset) {
    return new Promise( async (resolve) => {
      const releaseTarget = await this.targetLock.acquire();

      if (!this.addLock.isLocked() && ((offset < 0 && this.lastExecuted < 0) ||
          (offset > 0 && this.lastExecuted >= this.sentences.length() - 1))) {
        releaseTarget();
        this.editorImpl.executeError('Hit front/end of notebook',
            {start: 0, end: 0});
        resolve();
        return;
      }

      this.executeTarget.offset += offset;
      releaseTarget();

      this.executeToTarget();
      resolve();
    });
  }

  /**
   * Executes the Coq code up to the given character
   *
   * @param {Number} executeTargetIndex in the content (not index)
   */
  async executeTo(executeTargetIndex) {
    return new Promise(async (resolve, reject) => {
      if (executeTargetIndex < 0) {
        reject(new Error('Cannot execute to negative index'));
        return;
      }

      const releaseTarget = await this.targetLock.acquire();

      this.executeTarget.index = executeTargetIndex;
      this.executeTarget.offset = 0;
      releaseTarget();

      this.executeToTarget();
      resolve();
    });
  }

  /**
   * TODO this should be run whenever the target changes
   * This will then start executing if nothing else is executing
   */
  async executeToTarget() {
    if (this.executeLock.isLocked() || this.addLock.isLocked()) {
      return;
    }

    const releaseAdd = await this.addLock.acquire();
    const releaseExecute = await this.executeLock.acquire();

    // Read the target for the next execution
    const releaseTarget = await this.targetLock.acquire();

    if (this.executeTarget.offset === 0 && this.executeTarget.index < 0) {
      releaseTarget();
      releaseExecute();
      releaseAdd();
      return;
    }

    const sentenceTarget = Math.min(this.targetToSentenceIndex(),
        this.sentences.length() - 1);

    this.executeTarget.index = -1;
    this.executeTarget.offset = sentenceTarget - this.lastExecuted;


    if (this.executeTarget.offset === 0) {
      if (sentenceTarget === -1) {
        this.editorImpl.executeSuccess('', -1, false);
      }
      releaseTarget();
      releaseExecute();
      releaseAdd();
      return;
    }

    this.executeTarget.offset = Math.max(this.executeTarget.offset - 1, 0);

    releaseTarget();
    if (sentenceTarget < 0) {
      if (this.lastExecuted >= 0) {
        this.editorImpl.executeStarted(-1);
        this.editorImpl.executeSuccess('', -1, false);
      }
      releaseExecute();
      releaseAdd();
      this.lastExecuted = -1;
      return;
    }
    this.editorImpl.executeStarted(this.sentences.endIndex(sentenceTarget));

    if (sentenceTarget > this.lastExecuted) {
      // First check if the sentence is valid
      let error = null;
      const start = this.sentences.beginIndex(sentenceTarget);
      const end = this.sentences.endIndex(sentenceTarget);
      const sentence = this.currentContent.slice(start, end,
          this.sentences.endIndex(sentenceTarget));

      try {
        this.validate(sentence);
      } catch (e) {
        error = e;
      }

      if (error) {
        this.editorImpl.executeError(error, {start: start, end: end});

        releaseAdd();
        releaseExecute();
        return;
      }

      this.serapiImpl.exec(this.sentences.id(this.lastExecuted + 1),
          () => {
            releaseAdd();
            // TODO implement proof finished
            this.targetLock.acquire().then((release) => {
              this.lastExecuted += 1;
              if (sentenceTarget === this.lastExecuted) {
                this.getGoalsAtSentence(this.lastExecuted,
                    (goal) => {
                      this.editorImpl.executeSuccess(goal,
                          this.sentences.endIndex(this.lastExecuted),
                          false);
                    }, this.editorImpl.message);
              } else {
                this.editorImpl.executeSuccess(null,
                    this.sentences.endIndex(this.lastExecuted),
                    false);
              }

              releaseExecute();
              release();
              this.executeToTarget();
            });
          },
          async (errorObj) => {
            releaseAdd();

            const error = errorObj.message;
            let errorBeginIndex = errorObj.beginIndex;
            let errorEndIndex = errorObj.endIndex;

            const sentenceWithError = this.sentences.get(this.lastExecuted + 1);

            if (errorBeginIndex === -1) {
              errorBeginIndex = 0;
            }
            if (errorEndIndex === -1) {
              errorEndIndex =
                sentenceWithError.endIndex - sentenceWithError.beginIndex;
            }

            this.editorImpl.executeError(error,
                errorBeginIndex + sentenceWithError.beginIndex,
                errorEndIndex + sentenceWithError.beginIndex);
            // TODO make sure no new execution is taking place
            const releaseTarget = await this.targetLock.acquire();
            const sentenceTarget = this.targetToSentenceIndex();

            if (sentenceTarget > this.lastExecuted) {
              this.executeTarget.index = -1;
              this.executeTarget.offset = 0;
            } else {
              this.executeTarget.offset = sentenceTarget - this.lastExecuted;
            }
            releaseTarget();
            releaseExecute();
            this.executeToTarget();
          });
    } else {
      this.lastExecuted = sentenceTarget;
      if (this.lastExecuted >= 0) {
        this.getGoalsAtSentence(this.lastExecuted,
            (goal) => {
              releaseExecute();
              releaseAdd();
              this.editorImpl.executeSuccess(goal,
                  this.sentences.endIndex(this.lastExecuted),
                  false);
            }, this.editorImpl.message);
        // TODO what errors should/can be handled here?
      } else {
        this.editorImpl.executeSuccess('', -1, false);
        releaseExecute();
        releaseAdd();
      }
    }
  }

  /**
   * Convert target index and offset to sentenceIndex
   * @return {number} the sentenceIndex to where to execute
   */
  targetToSentenceIndex() {
    let index = this.lastExecuted;
    if (this.executeTarget.index >= 0) {
      index = this.sentences.sentenceBeforeIndex(this.executeTarget.index);
    }
    return index + this.executeTarget.offset;
  }

  /**
   * Get the Abstract Syntax Tree (AST) of a given sentence.
   * @param {Number} sentenceNr  number of sentence to request AST from
   */
  getAST(sentenceNr) {
    this.serapiImpl.requestAST(sentenceNr,
        (obj) => {
          console.log(`Succesfully requested AST for ${obj.sentenceId}`);
          console.log(obj.sentenceAST);
          this.sentences.setASTforSID(obj.sentenceId, obj.sentenceAST);
        },
        () => {
          console.log(`Error in requesting AST for ${sentenceNr}`);
        });
  }

  /**
   * Gets the goals at the given index,
   * when no index supplied this is after the last executed sentence
   *
   * @param {Number} index  The index in the file
   * @param {function} onSuccess The callback function on success
   * @param {function} onError The callback function on error
   */
  getGoals(index, onSuccess, onError) {
    // TODO add things to make sure the goal is executed before getting it
    if (index < 0 || index > this.currentContent.length) {
      // Invalid sentence ID
      throw new Error(`invalid sentence ID: ${index}`);
    } else {
      let sentenceBefore = this.sentences.sentenceBeforeIndex(index);
      if (sentenceBefore < this.sentences.length() - 1) {
        // we want the goal of the selected sentence
        sentenceBefore++;
      }
      this.getGoalsAtSentence(sentenceBefore,
          onSuccess, onError);
    }
  }

  /**
   * Gets the goals at the given index,
   * when no index supplied this is after the last executed sentence
   *
   * @param {Number} sentenceIndex The sentence index
   * @param {function} onSuccess The callback function on success
   * @param {function} onError The callback function on error
   * @param {string} format The pp_format SerAPI should use for the output
   *    defaults to 'PpStr' (for other options, see SerAPI documentation)
   */
  getGoalsAtSentence(sentenceIndex, onSuccess, onError, format='PpStr') {
    if (sentenceIndex < 0 || sentenceIndex >= this.sentences.length()) {
      throw new Error(`Sentence index out of bounds ${sentenceIndex}`);
    }
    this.serapiImpl.goals(this.sentences.id(sentenceIndex),
        onSuccess, onError, format);
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
    if (!this.serapiImpl.isReady()) {
      // Wait until serapi is ready to receive input
      return;
    }

    this.serapiImpl.search(searchQuery, onResult, onDone);
  }

  /**
   * Executes a Coq vernac query
   * @param {string} inputQuery The vernac query to execute
   */
  query(inputQuery) {
    if (!this.serapiImpl.isReady()) {
      // Wait until serapi is ready to receive input
      return;
    }

    this.serapiImpl.query(inputQuery);
  }

  /**
   * Stop this instance of coq
   */
  stop() {
    this.serapiImpl.terminate();
  }
}

export default CoqSerapi;
