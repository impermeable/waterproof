import SerapiProcessor from '../util/SerapiProcessor';
import {
  getGoalsFromResponse, parseErrorResponse,
} from '../SerapiParser';
import * as Constants from '../SerapiConstants';
import {
  createExecuteCommand, createGoalCommand,
} from '../util/SerapiCommandFactory';

class SerapiExecutionProcessor extends SerapiProcessor {
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
  }

  async executeNext() {
    const stateRelease = await this.state.stateLock.acquire();
    if (this.state.target >= this.state.sentenceSize() - 1) {
      stateRelease();
      return Promise.resolve();
    }

    this.state.target++;

    return this._executeToTarget(stateRelease);
  }

  async executePrevious() {
    const stateRelease = await this.state.stateLock.acquire();
    if (this.state.target <= -1) {
      stateRelease();
      return Promise.resolve();
    }

    this.state.target--;

    return this._executeToTarget(stateRelease);
  }

  async reset() {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = -1;

    return this._executeToTarget(stateRelease);
  }

  async executeAll() {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = this.state.sentenceSize() - 1;

    return this._executeToTarget(stateRelease);
  }

  async executeTo(textIndex) {
    const stateRelease = await this.state.stateLock.acquire();
    this.state.target = Math.min(this.state.sentenceBeforeIndex(textIndex),
        this.state.sentenceSize() - 1);

    return this._executeToTarget(stateRelease);
  }

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

        releaseExecutionLock();
        return this._getGoal(this.state.target);
      }/* else if (this.state.target > this.state.sentenceSize() - 1) {
        targetValue = this.state.sentenceSize() - 1;
        this.state.target = this.state.sentenceSize() - 1;
      }*/

      this.editor.executeStarted(
          this.state.endIndexOfSentence(this.state.target));

      while (targetValue > this.state.lastExecuted) {
        const nextSentence = this.state.lastExecuted + 1;
        const executionFailed =
            await this._executeSentence(this.state.idOfSentence(nextSentence));

        stateRelease = await this.state.stateLock.acquire();

        if (executionFailed != null) {
          this.state.target = this.state.lastExecuted;
          error = this._parseError(executionFailed);
        }

        targetValue = this.state.target;
        if (!executionFailed && targetValue !== nextSentence) {
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
      this.editor.executeError(error.message, {
        start: error.beginIndex,
        end: error.endIndex,
      });
    }

    releaseExecutionLock();
    stateRelease();

    return Promise.resolve();
  }

  async _getGoal(index) {
    if (index < 0) {
      this.editor.executeSuccess('', -1, false);
      return Promise.resolve();
    }
    const sentenceId = this.state.idOfSentence(index);
    const sentenceIndex = this.state.endIndexOfSentence(index);
    return this.sendCommand(createGoalCommand(sentenceId), 'g')
        .then((result) => {
          this.editor.executeSuccess(result.goal, sentenceIndex, false);
        });
  }

  async _executeSentence(sentenceId) {
    return this.sendCommand(createExecuteCommand(sentenceId), 'e')
        .then((result) => {
          if (result.hasOwnProperty('error')) {
            return result.error;
          } else {
            this.state.lastExecuted++;
            return null;
          }
        });
  }


  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'g') {
      return {
        goal: getGoalsFromResponse(data),
      };
    } else if (extraTag === 'e') {
      if (data[0] === Constants.COQ_EXCEPTION) {
        return {
          error: parseErrorResponse(data),
        };
      }
    }
  }

  handleSerapiFeedback(feedback, extraTag) {
  }
}

export default SerapiExecutionProcessor;
