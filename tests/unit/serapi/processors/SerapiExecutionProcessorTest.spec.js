import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiExecutionProcessor
  from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

describe('serapi execution processor', () => {
  let proc;
  let worker;
  const editor = new EditorInterface();

  const setLastExecuted = function(num) {
    if (proc != null) {
      proc.state.lastExecuted = num;
      proc.state.target = num;
    } else {
      console.log('Warning, proc not loaded in time');
    }
  };

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');

    proc = new SerapiExecutionProcessor(
        new SerapiTagger(worker, () => {}),
        new SerapiState(),
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should execute a sentence if execute next is called', async () => {
    proc.state.concatSentences([
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

    return proc.executeNext().then(() => {
      expect(worker.getCallAmount()).to.equal(2);

      expect(editor.executeStarted.callCount).to.be.at.least(1);
      expect(editor.executeSuccess.callCount).to.equal(1);
      // TODO: check params of success

      expect(proc.state.lastExecuted).to.equal(0);
    });
  });


  it('should not execute anything if already executed all sentences',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
        ]);

        setLastExecuted(0);

        return proc.executeNext().then(() => {
          expect(worker.getCallAmount()).to.equal(0);

          expect(editor.executeStarted.callCount).to.equal(0);
          expect(editor.executeSuccess.callCount).to.equal(0);
          // TODO: check params of success

          expect(proc.state.lastExecuted).to.equal(0);
        });
      });

  it('should not call anything if reverting first sentence', async () => {
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
    ]);

    setLastExecuted(0);

    return proc.executePrevious().then(() => {
      expect(worker.getCallAmount()).to.equal(0);

      expect(editor.executeSuccess.callCount).to.equal(1);
      // TODO: check params of success

      expect(proc.state.lastExecuted).to.equal(-1);
    });
  });

  it('should only call goal if reverting a sentence', async () => {
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
      {
        beginIndex: 7,
        endIndex: 12,
        sentenceId: 3,
      },
    ]);

    setLastExecuted(1);

    worker.addExpectedCall('Query ((sid 2', [
      'Ack',
      '(ObjList())',
      'Completed',
    ]);

    return proc.executePrevious().then(() => {
      expect(worker.getCallAmount()).to.equal(1);

      expect(editor.executeSuccess.callCount).to.equal(1);
      // TODO: check params of success

      expect(proc.state.lastExecuted).to.equal(0);
    });
  });

  it('should \'store\' calls to execute while busy and only show goal once',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 12,
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
        ], async () => {
          await proc.executeNext();
        });


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
        ]);


        await proc.executeNext();

        expect(worker.getCallAmount()).to.equal(3);
        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.lastCall.args[1]).to.equal(12);

        // only one goal call
      });

  it('should \'store\' calls to execute while busy and show goal in-between',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 12,
            sentenceId: 3,
          },
        ]);
        const firstGoal = '1 G';
        const finalGoal = '2 F';

        let duringCall = Promise.resolve();

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
          `(ObjList((CoqString"${firstGoal}")))`,
          'Completed',
        ], async () => {
        // here goal was just sent
          duringCall = proc.executeNext();
        });

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
          `(ObjList((CoqString"${finalGoal}")))`,
          'Completed',
        ]);


        await proc.executeNext();
        await duringCall;

        expect(worker.getCallAmount()).to.equal(4);
        expect(editor.executeStarted.callCount).to.equal(2);
        expect(editor.executeSuccess.callCount).to.be.at.least(2);
        expect(editor.executeSuccess.lastCall.args[0]).to.equal(finalGoal);
      });

  it('should give errors when they occur and not call goal', async () => {
    proc.state.concatSentences([{
      beginIndex: 0,
      endIndex: 8,
      sentenceId: 2,
    }]);

    const bp = 6;
    const ep = 7;
    const errorString = 'The reference a was not found in the current' +
      ' environment.';


    // note feedback is currently not used for the error message
    worker.addExpectedCall(`Exec 2`, [
      'Ack',
      '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message ' +
      'Error(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
      '(bol_pos_last 0)(bp 6)(ep 7)))(Pp_glue((Pp_string"The reference")' +
      '(Pp_print_break 1 0)(Pp_string a)(Pp_print_break 1 0)' +
      '(Pp_string"was not found")(Pp_print_break 1 0)(Pp_string"in ' +
      'the current")(Pp_print_break 1 0)(Pp_string environment.)))))))',
      `(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)` +
      `(bol_pos_last 0)(bp ${bp})(ep ${ep})))((1 2))(Backtrace())` +
      `(ExplainErr.EvaluatedError"${errorString}"))`,
      'Completed',
    ]);

    await proc.executeNext();

    expect(worker.getCallAmount()).to.equal(1);

    expect(proc.state.target).to.equal(-1);
    expect(editor.executeStarted.callCount).to.be.at.least(1);
    expect(editor.executeSuccess.callCount).to.equal(0);
    expect(editor.executeError.callCount).to.equal(1);
    expect(editor.executeError.lastCall.args[0]).to.equal(errorString);
    expect(editor.executeError.lastCall.args[1]).to.include({
      start: bp,
      end: ep,
    });
  });

  it('should cancel execution if error occurs in not last sentence',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 8,
            sentenceId: 2,
          },
          {
            beginIndex: 9,
            endIndex: 17,
            sentenceId: 3,
          },
        ]);

        const bp = 6;
        const ep = 7;
        const errorString = 'The reference a was not found in the current' +
          ' environment.';


        // note feedback is currently not used for the error message
        worker.addExpectedCall(`Exec 2`, [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
        '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message ' +
        'Error(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
        '(bol_pos_last 0)(bp 6)(ep 7)))(Pp_glue((Pp_string"The reference")' +
        '(Pp_print_break 1 0)(Pp_string a)(Pp_print_break 1 0)' +
        '(Pp_string"was not found")(Pp_print_break 1 0)(Pp_string"in ' +
        'the current")(Pp_print_break 1 0)(Pp_string environment.)))))))',
          `(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
          `(line_nb_last 1)(bol_pos_last 0)(bp ${bp})(ep ${ep})))((1 2))` +
          `(Backtrace())(ExplainErr.EvaluatedError"${errorString}"))`,
          'Completed',
        ]);

        await proc.executeAll();

        expect(worker.getCallAmount()).to.equal(1);
        expect(proc.state.target).to.equal(-1);


        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeSuccess.callCount).to.equal(0);
        expect(editor.executeError.callCount).to.equal(1);
        expect(editor.executeError.lastCall.args[0]).to.equal(errorString);
        expect(editor.executeError.lastCall.args[1]).to.include({
          start: bp,
          end: ep,
        });
      });

  it('should parse error index of not first sentence and should update goal',
      async () => {
        const sentenceBaseIndex = 9;
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 8,
            sentenceId: 2,
          },
          {
            beginIndex: sentenceBaseIndex,
            endIndex: 17,
            sentenceId: 3,
          },
        ]);

        setLastExecuted(0);

        const bp = 6;
        const ep = 7;
        const errorString = 'The reference a was not found in the current' +
      ' environment.';

        const previousGoal = 'GOAL_SENTENCE_2';


        // note feedback is currently not used for the error message
        worker.addExpectedCall(`Exec 3`, [
          'Ack',
          '(Feedback((doc_id 0)(span_id 2)(route 0)' +
      '(contents(ProcessingIn master))))',
          '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
          '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message ' +
      'Error(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
      '(bol_pos_last 0)(bp 6)(ep 7)))(Pp_glue((Pp_string"The reference")' +
      '(Pp_print_break 1 0)(Pp_string a)(Pp_print_break 1 0)' +
      '(Pp_string"was not found")(Pp_print_break 1 0)(Pp_string"in ' +
      'the current")(Pp_print_break 1 0)(Pp_string environment.)))))))',
          `(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
      `(line_nb_last 1)(bol_pos_last 0)(bp ${bp})(ep ${ep})))((1 2))` +
      `(Backtrace())(ExplainErr.EvaluatedError"${errorString}"))`,
          'Completed',
        ]);

        worker.addExpectedCall('Query ((sid 2', [
          'Ack',
          `(ObjList((CoqString"${previousGoal}")))`,
          'Completed',
        ]);


        await proc.executeAll();

        expect(worker.getCallAmount()).to.equal(2);
        expect(proc.state.target).to.equal(0);

        expect(editor.executeStarted.callCount).to.be.at.least(1);
        expect(editor.executeError.callCount).to.equal(1);
        expect(editor.executeError.lastCall.args[0]).to.equal(errorString);
        expect(editor.executeError.lastCall.args[1]).to.include({
          start: sentenceBaseIndex + bp,
          end: sentenceBaseIndex + ep,
        });

        expect(editor.executeSuccess.callCount).to.equal(1);
        expect(editor.executeSuccess.lastCall.args[0]).to.equal(previousGoal);
      });
});
