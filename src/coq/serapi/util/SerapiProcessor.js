import SerapiCallbacks from './SerapiCallbacks';
import * as Constants from '../SerapiConstants';

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
          (f) => this.handleFeedback(f), extraTag);
    }));
  }

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

  _addToResult(partial) {
    if (partial !== undefined) {
      this.commandStatus.result =
          Object.assign(this.commandStatus.result, partial);
    }
  }

  handleMessage(data, extraTag) {
    this._addToResult(this.handleSerapiMessage(data, extraTag));
    if (data === Constants.MESSAGE_COMPLETED) {
      // command completed resolve promise
      this._resolveCommand();
    }
  }

  handleFeedback(data) {
    this._addToResult(
        this.handleSerapiFeedback(data, this.commandStatus.extraTag));
  }

  handleSerapiMessage(data, extraTag) {
  }

  handleSerapiFeedback(feedback, extraTag) {
  }
}

export default SerapiProcessor;
