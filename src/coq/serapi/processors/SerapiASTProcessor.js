import SerapiProcessor from '../util/SerapiProcessor';
import {createASTCommand} from '../util/SerapiCommandFactory';
import {extractCoqAST} from '../ASTProcessor';

class SerapiASTProcessor extends SerapiProcessor {
  /**
   *
   * @param {SerapiTagger} tagger
   * @param {SerapiState} state
   * @param {EditorInterface} editor
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
  }

  async getAllAsts() {
    const stateRelease = await this.state.stateLock.acquire();
    for (let i = 0; i < this.state.sentenceSize(); i++) {
      await this._fetchASTFor(this.state.idOfSentence(i));
    }
    stateRelease();
    return Promise.resolve();
  }

  async getAstForSentence(sentenceIndex) {
    const stateRelease = await this.state.stateLock.acquire();
    await this._fetchASTFor(this.state.idOfSentence(sentenceIndex));
    stateRelease();
    return Promise.resolve();
  }

  async _fetchASTFor(sentenceId) {
    return this.sendCommand(createASTCommand(sentenceId), 'ast')
        .then((result) => {
          this.state.setASTforSID(sentenceId, result.ast);
          return Promise.resolve();
        });
  }

  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'ast') {
      return {
        ast: extractCoqAST(data),
      };
    }
  }

  handleSerapiFeedback(feedback, extraTag) {
    console.log('should not get any feedback');
  }
}


export default SerapiASTProcessor;
