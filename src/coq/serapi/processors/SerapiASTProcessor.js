import SerapiProcessor from '../util/SerapiProcessor';

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

  async getAstForSentence(sentenceIndex) {

  }

  handleSerapiMessage(data, extraTag) {
  }

  handleSerapiFeedback(feedback, extraTag) {
  }
}


export default SerapiASTProcessor;
