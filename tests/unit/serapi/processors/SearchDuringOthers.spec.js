import SerapiContentProcessor
  from '../../../../src/coq/serapi/processors/SerapiContentProcessor';
import SerapiExecutionProcessor
  from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';
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
  let execProc;
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

    execProc = new SerapiExecutionProcessor(tagger, state, editor);

    searchProc = new SerapiSearchProcessor(tagger, state, editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  // TODO: these tests are not great since they just test the worker calls
  // but should really test deadlocks etc.

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
      'Completed',
    ], async () => {
      duringPromise = searchProc.searchFor(query, onResult, onDone);
    });

    worker.addExpectedCall(`Vernac "Check (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await contentProc.setContent(text);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(4);

    expect(worker.getCall(0).toLowerCase()).to.include('add');

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);

    expect(contentProc.state.sentenceSize()).to.equal(1);
    expect(contentProc.state.idOfSentence(0)).to.equal(2);
  });

  it('should handle searching after set content', async () => {
    const text = 'Lemma a n:n+0=n.';
    const query = 'add';
    const onResult = sinon.fake();
    const onDone = sinon.fake();

    worker.addExpectedCall(text, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ]);

    worker.addExpectedCall(`Vernac "Check (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await contentProc.setContent(text);
    await searchProc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(4);

    expect(worker.getCall(0).toLowerCase()).to.include('add');

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);

    expect(contentProc.state.sentenceSize()).to.equal(1);
    expect(contentProc.state.idOfSentence(0)).to.equal(2);
  });

  it('should handle searching after execution', async () => {
    const query = 'add';
    const onResult = sinon.fake();
    const onDone = sinon.fake();

    execProc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    worker.addExpectedCall('Exec 2', [
      'Ack',
      '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
      'Completed',
    ]);

    worker.addExpectedCall('Query ((sid 2', [
      'Ack',
      '(ObjList())',
      'Completed',
    ]);

    worker.addExpectedCall(`Vernac "Check (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await execProc.executeNext();
    await searchProc.searchFor(query, onResult, onDone);
    expect(worker.getCallAmount()).to.equal(5);

    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(1);
    // TODO: check params of success

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);

    expect(execProc.state.lastExecuted).to.equal(0);
  });

  it('should wait for execution to start searching', async () => {
    const query = 'add';
    const onResult = sinon.fake();
    const onDone = sinon.fake();

    let duringPromise = Promise.resolve();

    execProc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    worker.addExpectedCall('Exec 2', [
      'Ack',
      '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
      'Completed',
    ], async () => {
      duringPromise = searchProc.searchFor(query, onResult, onDone);
    });

    worker.addExpectedCall('Query ((sid 2', [
      'Ack',
      '(ObjList())',
      'Completed',
    ]);

    worker.addExpectedCall(`Vernac "Check (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await execProc.executeNext();
    await duringPromise;
    expect(worker.getCallAmount()).to.equal(5);

    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(1);
    // TODO: check params of success

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);

    expect(execProc.state.lastExecuted).to.equal(0);
  });

  it('should wait for query of execution to start searching', async () => {
    const query = 'add';
    const onResult = sinon.fake();
    const onDone = sinon.fake();

    let duringPromise = Promise.resolve();

    execProc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    worker.addExpectedCall('Exec 2', [
      'Ack',
      '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
      'Completed',
    ]);

    worker.addExpectedCall('Query ((sid 2', [
      'Ack',
      '(ObjList())',
      'Completed',
    ], async () => {
      duringPromise = searchProc.searchFor(query, onResult, onDone);
    });

    worker.addExpectedCall(`Vernac "Check (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    await execProc.executeNext();
    await duringPromise;
    expect(worker.getCallAmount()).to.equal(5);

    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(1);
    // TODO: check params of success

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);

    expect(execProc.state.lastExecuted).to.equal(0);
  });
});
