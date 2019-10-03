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
      await this._setASTFor(this.state.idOfSentence(i));
    }
    stateRelease();
  }

  async getAstForSentence(sentenceIndex) {
    const stateRelease = await this.state.stateLock.acquire();
    await this._setASTFor(this.state.idOfSentence(sentenceIndex));
    stateRelease();
  }

  async _setASTFor(sentenceId) {
    return this.sendCommand(createASTCommand(sentenceId), 't')
        .then((ast) => {
          this.state.setASTforSID(sentenceId, ast);
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
