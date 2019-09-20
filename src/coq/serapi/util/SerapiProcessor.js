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

  handleMessage(data, extraTag) {
    const partialResult = this.handleSerapiMessage(data, extraTag);
    if (partialResult !== undefined) {
      this.commandStatus.result =
          Object.assign(this.commandStatus.result, partialResult);
    }
    if (data === Constants.MESSAGE_COMPLETED) {
      // command completed resolve promise
      this._resolveCommand();
    }
  }

  handleSerapiMessage(data, extraTag) {
  }
}

export default SerapiProcessor;
