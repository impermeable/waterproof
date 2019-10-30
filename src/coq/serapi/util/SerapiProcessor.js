import SerapiCallbacks from './SerapiCallbacks';
import {isGeneralMessage, MESSAGE_COMPLETED} from '../SerapiParser';

/**
 * The interface for a SerapiProcessor (And SerapiCallbacks)
 * Passes commands through and collects the results of each partial command
 * @interface
 */
class SerapiProcessor extends SerapiCallbacks {
  /**
   *
   * @param {SerapiTagger} tagger
   * @param {SerapiState} state
   * @param {EditorInterface} editor
   */
  constructor(tagger, state, editor) {
    super();
    this.tagger = tagger;
    this.state = state;
    this.editor = editor;

    this.commandStatus = {
      resolver: null,
      result: {},
      extraTag: null,
    };
    this.afterCommand = null;
  }

  /**
   * Send command to serapi with an optional tag
   * @param {String} command the command
   * @param {String} extraTag an extra identifying tag
   * @return {Promise<*|Promise<unknown>>} a promise which resolves
   *   when the command is complete
   */
  async sendCommand(command, extraTag=null) {
    if (this.commandStatus.resolver != null) {
      console.log('message send before last message resolved');
    }
    return new Promise(((resolve) => {
      this.commandStatus = {
        resolver: resolve,
        result: {},
        extraTag,
      };
      this.tagger.sendCommand(command,
          (m, t) => this.handleMessage(m, t),
          (f, raw) => {
            if (!raw) {
              this.handleFeedback(f);
            }
          }, extraTag);
    }));
  }


  /**
   * Called when command is finished
   * @private
   */
  _resolveCommand() {
    if (this.commandStatus.resolver != null) {
      const resolve = this.commandStatus.resolver;
      const resultObj = this.commandStatus.result;
      this.commandStatus = {
        resolver: null,
        result: {},
      };
      // call resolve with complete object
      resolve(resultObj);
    }
  }

  /**
   * Add part to result
   * @param {Object} partial the part to be added
   * @private
   */
  _addToResult(partial) {
    if (partial !== undefined) {
      this.commandStatus.result =
          Object.assign(this.commandStatus.result, partial);
    }
  }

  /**
   * Handle a serapi message
   * Passes through to handleSerapiMessage
   * @param {*} data the message
   * @param {String} extraTag the tag of the message
   */
  handleMessage(data, extraTag) {
    if (!isGeneralMessage(data)) {
      this._addToResult(this.handleSerapiMessage(data, extraTag));
    }
    if (data === MESSAGE_COMPLETED) {
      // command completed resolve promise
      this._resolveCommand();
    }
  }

  /**
   * Handle serapi feedback
   * Passes through to handleSerapiFeedback
   * @param {*} data the feedback
   */
  handleFeedback(data) {
    this._addToResult(
        this.handleSerapiFeedback(data, this.commandStatus.extraTag));
  }
}

export default SerapiProcessor;
