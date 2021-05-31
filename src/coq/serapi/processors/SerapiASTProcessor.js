import SerapiProcessor from '../util/SerapiProcessor';
import {createASTCommand} from '../util/SerapiCommandFactory';
import {extractCoqAST, currentlyNotParsedTypes} from '../ASTProcessor';

/**
 * Processor for ast handling
 */
class SerapiASTProcessor extends SerapiProcessor {
  /**
   * Create a SerapiASTProcessor
   * @param {SerapiTagger} tagger the tagger to use
   * @param {SerapiState} state the state to use
   * @param {EditorInterface} editor the editor to use
   */
  constructor(tagger, state, editor) {
    super(tagger, state, editor);
  }

  /**
   * Fetch all the asts for the current state
   */
  async getAllAsts() {
    const stateRelease = await this.state.stateLock.acquire();
    for (let i = 0; i < this.state.sentenceSize(); i++) {
      await this._fetchASTFor(this.state.idOfSentence(i));
    }
    stateRelease();
    return Promise.resolve();
  }

  // eslint-disable-next-line require-jsdoc
  getUnparsedTypes() {
    return currentlyNotParsedTypes;
  }
  /**
   * Fetch the asts for a specific sentence
   * @param {Number} sentenceIndex the index of the sentence
   */
  async getAstForSentence(sentenceIndex) {
    const stateRelease = await this.state.stateLock.acquire();
    await this._fetchASTFor(this.state.idOfSentence(sentenceIndex));
    stateRelease();
    return Promise.resolve();
  }

  /**
   * Fetch AST from serapi
   * @param {Number} sentenceId the sentence id of the sentence
   * @return {Promise<*>}
   * @private
   */
  async _fetchASTFor(sentenceId) {
    return this.sendCommand(createASTCommand(sentenceId), 'ast')
        .then((result) => {
          this.state.setASTforSID(sentenceId, result.ast);
          // for now just print json repr
          console.log(`Got AST for ${sentenceId}: `,
              JSON.parse(JSON.stringify(result.ast)));
        });
  }

  /**
   * Handle a serapi message
   * @param {*} data the serapi message (parsed)
   * @param {String} extraTag the extra identifying tag
   * @return {*} partial of this command
   */
  handleSerapiMessage(data, extraTag) {
    if (extraTag === 'ast') {
      return {
        ast: extractCoqAST(data),
      };
    }
  }
}


export default SerapiASTProcessor;
