import SerapiContentProcessor
  from '../../../../src/coq/serapi/processors/SerapiContentProcessor';
// import SerapiExecutionProcessor
//   from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';
import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiSearchProcessor
  from '../../../../src/coq/serapi/processors/SerapiSearchProcessor';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

const emptyResponse = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  '(ObjList())',
  'Completed'];

describe('serapi combined content & execution processor', () => {
  let contentProc;
  // let execProc;
  let searchProc;

  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'setContentSuccess');
    sinon.spy(editor, 'setContentError');
    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');

    const tagger = new SerapiTagger(worker, () => {
    });
    const state = new SerapiState();

    contentProc = new SerapiContentProcessor(tagger, state, editor);

    // execProc = new SerapiExecutionProcessor(tagger, state, editor);

    searchProc = new SerapiSearchProcessor(tagger, state, editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should wait for content to be resolved until searching', async () => {
    const text = 'Lemma a n:n+0=n.';
    const query = 'add';
    const onResult = sinon.fake();
    const onDone = sinon.fake();

    let duringPromise = Promise.resolve();

    worker.addExpectedCall(text, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
    ], async () => {
      duringPromise = searchProc.searchFor(query, onResult, onDone);
    });

    worker.addExpectedCall(`Vernac "Check (${query})."`,
        ['(Answer wp0-a Completed)'].concat(emptyResponse));

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await contentProc.setContent(text);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(4);

    expect(worker.getCall(0).toLowerCase()).to.include('add');

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(contentProc.state.sentenceSize()).to.equal(1);
    expect(contentProc.state.idOfSentence(0)).to.equal(2);
  });
});
