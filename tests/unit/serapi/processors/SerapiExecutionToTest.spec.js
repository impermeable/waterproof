import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiExecutionProcessor
  from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

describe('serapi execute to processor', () => {
  let proc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');

    proc = new SerapiExecutionProcessor(
        new SerapiTagger(worker, null),
        new SerapiState(),
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should a sentence if index right after dot', async () => {
    // example content: 'Proof.' length: 6
    const endIndex = 6;
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: endIndex,
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

    worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpStr', [
      'Ack',
      '(ObjList())',
      'Completed',
    ]);

    worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpSer', [
      'Ack',
      '(ObjList())',
      'Completed',
    ]);


    return proc.executeTo(endIndex + 1).then(() => {
      expect(worker.getCallAmount()).to.equal(3);

      expect(editor.executeStarted.callCount).to.be.at.least(1);
      expect(editor.executeSuccess.callCount).to.equal(1);
      // TODO: check params of success

      expect(proc.state.lastExecuted).to.equal(0);
    });
  });

  it('should not execute anything if at front of content', async () => {
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    return proc.executeTo(0).then(() => {
      expect(worker.getCallAmount()).to.equal(0);

      expect(editor.executeStarted.callCount).to.equal(0);
      expect(editor.executeSuccess.callCount).to.equal(0);
      expect(editor.executeError.callCount).to.equal(0);

      expect(proc.state.sentenceSize()).to.equal(1);
      expect(proc.state.lastExecuted).to.equal(-1);
    });
  });

  [-1, 0, 1, 100].forEach((index) =>
    it(`should not execute anything if there are no sentences, index: ${index}`,
        async () => {
          return proc.executeTo(index).then(() => {
            expect(worker.getCallAmount()).to.equal(0);

            expect(editor.executeStarted.callCount).to.equal(0);
            expect(editor.executeSuccess.callCount).to.equal(0);
            expect(editor.executeError.callCount).to.equal(0);

            expect(proc.state.lastExecuted).to.equal(-1);
          });
        }));

  it('should not execute the sentence the index is in', async () => {
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    return proc.executeTo(3).then(() => {
      expect(worker.getCallAmount()).to.equal(0);

      expect(editor.executeStarted.callCount).to.equal(0);
      expect(editor.executeSuccess.callCount).to.equal(0);
      expect(editor.executeError.callCount).to.equal(0);

      expect(proc.state.lastExecuted).to.equal(-1);
    });
  });

  it('should execute the sentence before the sentence of the index',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 14,
            sentenceId: 3,
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

        worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpStr', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpSer', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        return proc.executeTo(10).then(() => {
          expect(worker.getCallAmount()).to.equal(3);

          expect(editor.executeStarted.callCount).to.be.at.least(1);
          expect(editor.executeSuccess.callCount).to.equal(1);
          // TODO: check params of success

          expect(proc.state.lastExecuted).to.equal(0);
        });
      });

  it('should do the latest call of executeTo if after current',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 14,
            sentenceId: 3,
          },
        ]);

        let duringPromise = Promise.resolve();

        worker.addExpectedCall('Exec 2', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
          '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          'Completed',
        ], async () => {
          duringPromise = proc.executeTo(15);
        });

        worker.addExpectedCall('Exec 3', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 3)(route 0)' +
          '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 3)(route 0)(contents Processed)))',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 3)(pp ((pp_format PpStr', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 3)(pp ((pp_format PpSer', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);


        await proc.executeTo(7);
        await duringPromise;
        expect(worker.getCallAmount()).to.equal(4);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(2);
        // TODO: check params of success

        expect(proc.state.lastExecuted).to.equal(1);
      });

  it('should do the latest call of executeTo if before current',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 14,
            sentenceId: 3,
          },
        ]);

        let duringPromise = Promise.resolve();

        worker.addExpectedCall('Exec 2', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
        '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          'Completed',
        ], async () => {
          duringPromise = proc.executeTo(7);
        });

        worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpStr', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 2)(pp ((pp_format PpSer', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);


        await proc.executeTo(15);
        await duringPromise;
        expect(worker.getCallAmount()).to.equal(3);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(1);
        // TODO: check params of success

        expect(proc.state.lastExecuted).to.equal(0);
      });

  it('should process a execute next during execute to',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 14,
            sentenceId: 3,
          },
        ]);

        let duringPromise = Promise.resolve();

        worker.addExpectedCall('Exec 2', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
        '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          'Completed',
        ], async () => {
          duringPromise = proc.executeNext();
        });

        worker.addExpectedCall('Exec 3', [
          'Ack',
          '(Feedback((doc_id 0)(span_id 3)(route 0)' +
        '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 3)(route 0)(contents Processed)))',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 3)(pp ((pp_format PpStr', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 3)(pp ((pp_format PpSer', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);


        await proc.executeTo(7);
        await duringPromise;
        expect(worker.getCallAmount()).to.equal(4);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(2);
        // TODO: check params of success

        expect(proc.state.lastExecuted).to.equal(1);
      });

  // it('should \'overwrite\' a previous executeNext', async () => {
  //   executeNext();
  //   // while running
  //   executeTo(0);
  // });
  //
  // it('should \'overwrite\' a previous executePrevious', async () => {
  //   executePrevious();
  //   // while running
  //   executeTo(100);
  // });
  //
  // it('should process executeNext after executeTo is done', async () => {
  //   executeTo();
  //   // while running
  //   executeNext();
  // });
  //
  // it('should process executePrevious after executeTo is done', async () => {
  //   executeTo();
  //   // while running
  //   executePrevious();
  // });
});
