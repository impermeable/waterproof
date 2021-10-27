import SerapiProcessor from '../util/SerapiProcessor';
import {
  COQ_EXCEPTION,
  getGoalsFromResponse,
  detectUnfocusedGoal,
  parseErrorResponse,
} from '../SerapiParser';
import {
  createExecuteCommand,
  createGoalCommand,
} from '../util/SerapiCommandFactory';

/**
 * Processor for execution and getting goals after execution
 */
class SerapiExecutionProcessor extends SerapiProcessor {
  /**
   * Create a SerapiExecutionProcessor
   * @param {SerapiTagger} tagger the tagger to use
   * @param {SerapiState} state the state to use
   * @param {EditorInterface} editor the editor to use
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
  }

  /**
   * Executes the next Coq sentence
   */
  async executeNext() {
    const stateRelease = await this.state.stateLock.acquire();
    if (this.state.target >= this.state.sentenceSize() - 1) {
      stateRelease();
      return Promise.resolve();
    }

    this.state.target++;

    return this._executeToTarget(stateRelease);
  }

  /**
   * Rolls back the last Coq sentence
   */
  async executePrevious() {
    const stateRelease = await this.state.stateLock.acquire();
    if (this.state.target <= -1) {
      stateRelease();
      return Promise.resolve();
    }

    this.state.target--;

    return this._executeToTarget(stateRelease);
  }

  /**
   * Revert all execution
   */
  async reset() {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = -1;

    return this._executeToTarget(stateRelease);
  }

  /**
   * Execute all sentences
   */
  async executeAll() {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = this.state.sentenceSize() - 1;

    return this._executeToTarget(stateRelease);
  }

  /**
   * Executes Coq code until the provided index
   *
   * @param {Number} textIndex The index of the cursor
   */
  async executeTo(textIndex) {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = Math.min(this.state.sentenceBeforeIndex(textIndex),
        this.state.sentenceSize() - 1);

    return this._executeToTarget(stateRelease);
  }

  /**
   * Parse an execution error
   * @param {*} error the error
   * @return {any} a error which the editor interface understands
   * @private
   */
  _parseError(error) {
    const sentenceIndex = this.state.lastExecuted + 1;
    if (error.beginIndex === -1) {
      // no precise location just mark full sentence
      return Object.assign(error, {
        beginIndex: this.state.beginIndexOfSentence(sentenceIndex),
        endIndex: this.state.endIndexOfSentence(sentenceIndex),
      });
    }

    const sentenceOffset = this.state.beginIndexOfSentence(sentenceIndex);
    return Object.assign(error, {
      beginIndex: error.beginIndex + sentenceOffset,
      endIndex: error.endIndex + sentenceOffset,
    });
  }

  /**
   * Execute until target is reached (and update in the meanwhile)
   * @param {Function} stateRelease state lock release
   * @return {Promise<*>} promise which resolves when the command is done
   * @private
   */
  async _executeToTarget(stateRelease) {
    if (this.state.executionLock.isLocked()) {
      stateRelease();
      return Promise.resolve();
    }

    const releaseExecutionLock = await this.state.executionLock.acquire();

    let targetValue = this.state.target;
    let error = null;

    while (targetValue !== this.state.lastExecuted) {
      stateRelease();
      if (targetValue < this.state.lastExecuted) {
        this.state.lastExecuted = this.state.target;

        this._startPreviousGoal(this.state.target);

        releaseExecutionLock();
        return this._getGoal(this.state.target);
      }/* else if (this.state.target > this.state.sentenceSize() - 1) {
        targetValue = this.state.sentenceSize() - 1;
        this.state.target = this.state.sentenceSize() - 1;
      }*/

      while (targetValue > this.state.lastExecuted) {
        this.editor.executeStarted(
            this.state.endIndexOfSentence(this.state.target));
        const nextSentence = this.state.lastExecuted + 1;
        const sentenceId = this.state.idOfSentence(nextSentence);
        const execResult = await this._executeSentence(sentenceId);

        stateRelease = await this.state.stateLock.acquire();

        if (execResult.error != null) {
          this.state.target = this.state.lastExecuted;
          error = this._parseError(execResult.error);
        } else {
          const previousMessages =
              this.state.getSentenceByIndex(nextSentence).messages;

          if (previousMessages != null) {
            for (const message of previousMessages) {
              this.editor.message(message, sentenceId);
            }
          } else {
            this.state.getSentenceByIndex(nextSentence).messages =
                execResult.messages;
          }
        }

        targetValue = this.state.target;
        if (!execResult.error && targetValue !== nextSentence) {
          this.editor.executeSuccess(null,
              this.state.endIndexOfSentence(nextSentence), false);
        }
        stateRelease();
      }

      stateRelease = await this.state.stateLock.acquire();
      targetValue = this.state.target;
    }

    if (this.state.lastExecuted >= 0) {
      await this._getGoal(this.state.lastExecuted);
    }

    if (error != null) {
      this._startPreviousGoal(this.state.lastExecuted);
      this.editor.executeError(error.message, {
        start: error.beginIndex,
        end: error.endIndex,
      });
    }

    releaseExecutionLock();
    stateRelease();

    return Promise.resolve();
  }

  /**
   * Send command to get the goal at a certain sentence index
   * @param {Number} index the index of the sentence to execute
   * @return {Promise<*>} promise which resolves when the command is done
   * @private
   */
  async _getGoal(index) {
    if (index < 0) {
      this.editor.executeSuccess('', -1, false);
      return Promise.resolve();
    }
    const sentenceId = this.state.idOfSentence(index);
    const sentenceIndex = this.state.endIndexOfSentence(index);
    const baseGoal = await this.sendCommand(createGoalCommand(sentenceId), 'g');
    let goalString = baseGoal.goal;
    if (baseGoal.goal === '') {
      const serapiGoal = await this.sendCommand(
          createGoalCommand(sentenceId.toString(), 'PpSer'), 'k');
      if (serapiGoal.next_goal_message != null) {
        goalString += '\n';
        goalString += serapiGoal.next_goal_message;
      }
    }

    this.editor.executeSuccess(goalString, sentenceIndex, false);
    return goalString;
  }

  /**
   * Send command to execute a sentence (by sentence id)
   * @param {Number} sentenceId the id of the sentence to execute
   * @return {Promise<*>} promise which resolves when the command is done
   * @private
   */
  async _executeSentence(sentenceId) {
    const messages = [];
    return this.sendCommand(createExecuteCommand(sentenceId), 'e',
        (feedback) => {
          if (!feedback.errorFlag) {
            messages.push(feedback.string);
            this.editor.message(feedback.string, sentenceId);
          }
        })
        .then((result) => {
          if (result.hasOwnProperty('error')) {
            return {
              error: result.error,
              messages: messages,
            };
          } else {
            this.state.lastExecuted++;
            return {
              error: null,
              messages: messages,
            };
          }
        });
  }

  /**
   * Signals to the editor that we are reverting by 'starting' execution to
   * some previous index
   * @param {Number} index the sentence index of the the sentence to revert to
   * @private
   */
  _startPreviousGoal(index) {
    if (index < 0) {
      this.editor.executeStarted(-1);
    } else {
      this.editor.executeStarted(this.state.endIndexOfSentence(index));
    }
  }

  /**
   * Handle a serapi message
   * @param {*} data the serapi message (parsed)
   * @param {String} extraTag the extra identifying tag
   * @return {*} partial of this command
   */
  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'g') {
      return {
        goal: getGoalsFromResponse(data),
      };
    } else if (extraTag === 'k') {
      return detectUnfocusedGoal(data);
    } else if (extraTag === 'e') {
      if (data[0] === COQ_EXCEPTION) {
        return {
          error: parseErrorResponse(data),
        };
      }
    } else {
      console.log(`unknown tag ${extraTag} with data ${data}`);
    }
  }
}

export default SerapiExecutionProcessor;
