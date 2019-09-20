import SerapiContentProcessor
  from '../../../../src/coq/serapi/processors/SerapiContentProcessor';
import SerapiExecutionProcessor
  from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';
import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

describe('serapi combined content & execution processor', () => {
  let contentProc;
  let execProc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'setContentSuccess');
    sinon.spy(editor, 'setContentError');
    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');

    const tagger = new SerapiTagger(worker, () => {});
    const state = new SerapiState();

    contentProc = new SerapiContentProcessor(tagger, state, editor);

    execProc = new SerapiExecutionProcessor(tagger, state, editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should wait to start execution until content is set', async () => {
    // from empty content
    const text = 'Lemma a n:n+0=n.';

    let duringPromise = Promise.resolve();

    worker.addExpectedCall(text, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ], async () => {
      duringPromise = execProc.executeNext();
    });

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

    await contentProc.setContent(text);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(3);

    expect(worker.getCall(0).toLowerCase()).to.include('add');

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(contentProc.state.sentenceSize()).to.equal(1);
    expect(contentProc.state.idOfSentence(0)).to.equal(2);

    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(1);
    expect(editor.executeError.callCount).to.equal(0);
    // TODO: check params of success

    expect(execProc.state.lastExecuted).to.equal(0);
  });

  it('should rollback and cancel execution if content modified',
      async () => {
        // given two sentences
        const baseText = 'Lemma a n:n+0=n.';
        const fullText = baseText + ' Proof.';
        contentProc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 16,
            sentenceId: 2,
          },
          {
            beginIndex: 17,
            endIndex: 23,
            sentenceId: 3,
          },
        ]);
        contentProc.currentContent = fullText;

        let duringPromise = Promise.resolve();

        worker.addExpectedCall('Exec 2', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          'Completed',
        ]);

        worker.addExpectedCall('Exec 3', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 3)(route 0)' +
      '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 3)(route 0)(contents Processed)))',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 3', [
          'Ack',
          '(ObjList())',
          'Completed',
        ], async () => {
          duringPromise = contentProc.setContent(baseText);
        });

        worker.addExpectedCall('Query ((sid 2', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        worker.addExpectedCall('Cancel (3)', [
          'Ack',
          '(Canceled(3))',
          'Completed',
        ]);

        await execProc.executeAll();
        await duringPromise;

        expect(worker.getCallAmount()).to.equal(5);

        expect(editor.setContentSuccess.callCount).to.be.at.least(1);
        expect(editor.setContentError.callCount).to.equal(0);

        expect(contentProc.state.sentenceSize()).to.equal(1);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(1);
        expect(editor.executeError.callCount).to.equal(0);

        expect(execProc.state.lastExecuted).to.equal(0);
        expect(execProc.state.target).to.equal(0);
      });

  it('should only calculate executeTo after completion of setContent',
      async () => {
        // from initial sentence
        const initialText = 'Lemma a n:n+0=n.';
        contentProc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 16,
            sentenceId: 2,
          },
        ]);
        contentProc.currentContent = initialText;

        const finalText = 'Proof. Proof.';

        let duringPromise = Promise.resolve();

        worker.addExpectedCall('Cancel (2)', [
          'Ack',
          '(Canceled(2))',
          'Completed',
        ], async () => {
          duringPromise = execProc.executeTo(8);
        });

        worker.addExpectedCall(`"${finalText}"`, [
          'Ack',
          '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
            '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
          '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
            '(line_nb_last 1)(bol_pos_last 0)(bp 7)(ep 13))NewTip)',
          'Completed',
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

        await contentProc.setContent(finalText);
        await duringPromise;

        expect(worker.getCallAmount()).to.equal(4);

        expect(editor.setContentSuccess.callCount).to.be.at.least(1);
        expect(editor.setContentError.callCount).to.equal(0);

        expect(contentProc.state.sentenceSize()).to.equal(2);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(1);
        expect(editor.executeError.callCount).to.equal(0);
        // TODO: check params of success

        expect(execProc.state.target).to.equal(0);
        expect(execProc.state.lastExecuted).to.equal(0);
      });

  it('should not try to execute sentences that were not added', async () => {
    const newContent = 'Proof. P.';
    let duringPromise = Promise.resolve();


    worker.addExpectedCall(`"${newContent}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last ' +
        '1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      '(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last ' +
        '1)(bol_pos_last 0)(bp 7)(ep 8)))()(Backtrace())(Stream.Error"' +
        'illegal begin of vernac"))',
      'Completed',
    ], async () => {
      duringPromise = execProc.executeTo(10);
    });

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

    await contentProc.setContent(newContent);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(3);

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(1);

    expect(contentProc.state.sentenceSize()).to.equal(1);

    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(1);
    expect(editor.executeError.callCount).to.equal(0);
    // TODO: check params of success

    expect(execProc.state.target).to.equal(0);
    expect(execProc.state.lastExecuted).to.equal(0);
  });
});
