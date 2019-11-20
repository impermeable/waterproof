import SerapiContentProcessor
  from '../../../../src/coq/serapi/processors/SerapiContentProcessor';
import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

describe('serapi content processor', () => {
  let proc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'setContentSuccess');
    sinon.spy(editor, 'setContentError');
    sinon.spy(editor, 'executeStarted');

    proc = new SerapiContentProcessor(
        new SerapiTagger(worker, null),
        new SerapiState(),
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should send add command on content set', async () => {
    // from empty content
    const text = 'Lemma a n:n+0=n.';
    worker.addExpectedCall(`(Add () "${text}")`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ]);

    return proc.setContent(text).then(() => {
      expect(worker.getCall(0).toLowerCase()).to.include('add');

      expect(editor.setContentSuccess.callCount).to.be.at.least(1);
      expect(editor.setContentError.callCount).to.equal(0);

      expect(proc.state.sentenceSize()).to.equal(1);
      expect(proc.state.idOfSentence(0)).to.equal(2);
    });
  });

  it('should add the sentences in the right order', async () => {
    const text = 'Proof. Proof.';
    worker.addExpectedCall(`(Add () "${text}")`, [
      'Ack',
      '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 7)(ep 13))NewTip)',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      'Completed',
    ]);

    await proc.setContent(text);

    expect(editor.setContentSuccess.callCount).to.be.at.least(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(proc.state.sentenceSize()).to.equal(2);
    expect(proc.state.idOfSentence(0)).to.equal(2);
    expect(proc.state.idOfSentence(1)).to.equal(3);
  });

  it('should send cancel and add command on content modify', async () => {
    // Given 3 sentences
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
      {
        beginIndex: 7,
        endIndex: 13,
        sentenceId: 3,
      },
      {
        beginIndex: 14,
        endIndex: 20,
        sentenceId: 4,
      },
    ]);
    const baseText = 'Proof. Proof. ';
    proc.currentContent = baseText + 'Proof.';
    const extraText = 'Prof.';

    worker.addExpectedCall('Cancel (4)', [
      'Ack',
      '(Canceled(4))',
      'Completed',
    ]);

    worker.addExpectedCall(extraText, [
      'Ack',
      '(Added 5((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ]);


    return proc.setContent(baseText + extraText).then(() => {
      expect(worker.getCallAmount()).to.equal(2);

      expect(editor.setContentSuccess.callCount).to.be.at.least(1);
      expect(editor.setContentError.callCount).to.equal(0);

      // no response from add so should just have two sentences
      expect(proc.state.sentences).to.have.lengthOf(3);
      expect(proc.state.sentences[2].sentenceId).to.equal(5);
    });
  });

  it('should only cancel removed sentences if text cut and not add anything',
      async () => {
        const baseText = 'Lemma a n:n+0=n.';
        const fullText = baseText + ' Proof.';
        proc.state.concatSentences([
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
        proc.currentContent = fullText;

        worker.addExpectedCall('Cancel (3)', [
          'Ack',
          '(Canceled(3))',
          'Completed',
        ]);

        await proc.setContent(baseText);

        expect(worker.getCallAmount()).to.equal(1);
        expect(editor.setContentSuccess.callCount).to.be.at.least(1);
        expect(editor.setContentError.callCount).to.equal(0);
        expect(proc.state.sentences).to.have.lengthOf(1);
        expect(proc.state.idOfSentence(0)).to.equal(2);
      });

  it('should cancel all sentences if needed and set new content in second call',
      async () => {
        const startContent = 'Proof.';
        const secondContent = 'Lemma a n:n+0=n.';

        worker.addExpectedCall(`Add () "${startContent}"`, [
          'Ack',
          '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
        '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
          'Completed',
        ]);

        worker.addExpectedCall('Cancel (2', [
          'Ack',
          '(Canceled(2))',
          'Completed',
        ]);

        worker.addExpectedCall(`"${secondContent}"`, [
          'Ack',
          '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
        '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
          'Completed',
        ]);


        await proc.setContent(startContent);
        expect(worker.getCallAmount()).to.equal(1);

        expect(editor.setContentSuccess.callCount).to.be.at.least(1);
        expect(editor.setContentError.callCount).to.equal(0);

        // no response from add so should just have two sentences
        expect(proc.state.sentences).to.have.lengthOf(1);
        expect(proc.state.sentences[0].beginIndex).to.equal(0);
        expect(proc.state.sentences[0].endIndex).to.equal(6);
        expect(proc.currentContent).to.equal(startContent);

        await proc.setContent(secondContent);

        expect(worker.getCallAmount()).to.equal(3);

        expect(editor.setContentSuccess.callCount).to.be.at.least(2);
        expect(editor.setContentError.callCount).to.equal(0);

        // no response from add so should just have two sentences
        expect(proc.state.sentences).to.have.lengthOf(1);
        expect(proc.currentContent).to.equal(secondContent);
      });

  it('should reroll the goal if execution is beyond edit location',
      async () => {
        proc.state.concatSentences([
          {
            beginIndex: 0,
            endIndex: 6,
            sentenceId: 2,
          },
          {
            beginIndex: 7,
            endIndex: 13,
            sentenceId: 3,
          },
          {
            beginIndex: 14,
            endIndex: 20,
            sentenceId: 4,
          },
        ]);
        const baseText = 'Proof. Proof. ';
        proc.currentContent = baseText + 'Proof.';
        proc.state.lastExecuted = 2;
        // answer rerolled goal message
        worker.addExpectedCall('Goals', [
          'Ack',
          '(ObjList())',
          'Completed',
        ]);

        // answer cancel message
        worker.addExpectedCall('Cancel', [
          'Ack',
          '(Canceled(4))',
          'Completed',
        ]);

        const extraText = 'Prof.';
        worker.addExpectedCall(extraText + '"', [
          'Ack',
          '(Added 5((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
          'Completed',
        ]);

        return proc.setContent(baseText + extraText).then(() => {
          expect(worker.getCallAmount()).to.equal(3);

          expect(editor.setContentSuccess.callCount).to.be.at.least(1);
          expect(editor.setContentError.callCount).to.equal(0);
          expect(editor.executeStarted.callCount).to.be.at.least(1);
          expect(editor.executeStarted.lastCall.args[0]).to.equal(13);

          // no response from add so should just have two sentences
          expect(proc.state.sentences).to.have.lengthOf(3);
          expect(proc.state.sentences[2].sentenceId).to.equal(5);
          expect(proc.state.lastExecuted).to.equal(1);
        });
      });

  it('should cancel all setences if content cleared', async () => {
    // from empty content
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
      {
        beginIndex: 7,
        endIndex: 13,
        sentenceId: 3,
      },
      {
        beginIndex: 14,
        endIndex: 20,
        sentenceId: 4,
      },
    ]);
    proc.currentContent = 'Proof. Proof. Proof.';

    // answer cancel message
    worker.addExpectedCall('Cancel (2 3 4)', [
      'Ack',
      '(Canceled(2 3 4))',
      'Completed',
    ]);

    return proc.setContent('').then(() => {
      expect(worker.getCallAmount()).to.equal(1);

      expect(proc.state.sentenceSize()).to.equal(0);
    });
  });

  it('should update to new content if called while adding', async () => {
    const initialContent = 'Proof.';
    const duringContent = 'Lemma a n:n+0=n.';
    worker.addExpectedCall(`Add () "${initialContent}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      'Completed',
    ], async () => {
      await proc.setContent(duringContent);
    });

    worker.addExpectedCall('Cancel (2', [
      'Ack',
      '(Canceled(2))',
      'Completed',
    ]);

    worker.addExpectedCall(`"${duringContent}"`, [
      'Ack',
      '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ]);

    // TODO: should not final content reject a promise?
    await proc.setContent(initialContent);

    expect(worker.getCallAmount()).to.equal(3);

    expect(proc.state.sentenceSize()).to.equal(1);
    expect(proc.currentContent).to.equal(duringContent);
    expect(worker.getCall(2)).to.include(duringContent);
  });

  it('should only take the latest update of content', async () => {
    const initialContent = 'Proof.';
    const duringContentIntermediate = 'Check plus.';
    const duringContentFinal = 'Lemma a n:n+0=n.';
    let duringPromise = Promise.resolve();
    worker.addExpectedCall(`Add () "${initialContent}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      'Completed',
    ], () => {
      proc.setContent(duringContentIntermediate);
      duringPromise = proc.setContent(duringContentFinal);
    });

    worker.addExpectedCall('Cancel (2', [
      'Ack',
      '(Canceled(2))',
      'Completed',
    ]);

    worker.addExpectedCall(`"${duringContentFinal}"`, [
      'Ack',
      '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 16))NewTip)',
      'Completed',
    ]);

    // TODO: should not final content reject a promise?
    await proc.setContent(initialContent);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(3);

    expect(proc.state.sentenceSize()).to.equal(1);
    expect(proc.currentContent).to.equal(duringContentFinal);
  });

  it('should not call if the newContent only changed in between', async () => {
    const initialContent = 'Proof.';
    const duringContent = '';
    let duringPromise = Promise.resolve();
    worker.addExpectedCall(`Add () "${initialContent}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      'Completed',
    ], () => {
      // go to nothing and back
      proc.setContent(duringContent);
      duringPromise = proc.setContent(initialContent);
    });

    // TODO: should not final content reject a promise?
    await proc.setContent(initialContent);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(1);

    expect(proc.state.sentenceSize()).to.equal(1);
    expect(proc.currentContent).to.equal(initialContent);
  });

  it('should sanitize content correctly', async () => {
    const coqSentence = 'Proof.';
    const content = coqSentence + ' (* \\ "a" \\ *) ' + coqSentence;

    worker.addExpectedCall(`Add () "Proof. (* \\\\ \\"a\\" \\\\ *) Proof."`, [
      'Ack',
      '(Added 5((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      '(Added 6((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 21)(ep 27))NewTip)',
      'Completed',
    ]);

    await proc.setContent(content);

    expect(worker.getCallAmount()).to.equal(1);

    expect(proc.state.sentenceSize()).to.equal(2);
    expect(proc.state.endIndexOfSentence(0)).to.equal(6);
    expect(proc.state.beginIndexOfSentence(1)).to.equal(21);
    expect(proc.state.textOfSentence(0)).to.equal(coqSentence);
    expect(proc.state.textOfSentence(1)).to.equal(coqSentence);
  });

  it('should handle utf8 chars correctly and set correct indices', async () => {
    const content = 'Lemma a ε: ε+0=ε.';

    worker.addExpectedCall(`"${content}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 20))NewTip)',
      'Completed',
    ]);

    await proc.setContent(content);

    expect(content.length).to.not.equal(20);

    expect(worker.getCallAmount()).to.equal(1);

    expect(proc.state.sentenceSize()).to.equal(1);
    expect(proc.state.beginIndexOfSentence(0)).to.equal(0);
    expect(proc.state.endIndexOfSentence(0)).to.equal(content.length);
  });

  it('should give the error if one occurs at the beginning', async () => {
    const content = 'Lemma.';
    const errorString = '[Prim.ident_decl] expected after ' +
      '[vernac:thm_token] (in [vernac:gallina])';
    const bp = 5;
    const ep = 6;
    worker.addExpectedCall(`${content}`, [
      'Ack',
      '(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
      `(bol_pos_last 0)(bp ${bp})(ep ${ep})))()(Backtrace())(Stream.Error"` +
      errorString + '"))',
      'Completed',
    ]);

    await proc.setContent(content);

    expect(worker.getCallAmount()).to.equal(1);
    expect(proc.state.sentenceSize()).to.equal(0);
    expect(editor.setContentError.callCount).to.equal(1);
    expect(editor.setContentError.lastCall.args[0]).to.include({
      message: errorString,
      beginIndex: bp,
      endIndex: ep,
    });

    expect(editor.setContentSuccess.callCount).to.be.equal(0);
  });

  it('should resolve if content is corrected after error', async () => {
    const content = 'P.';
    const secondContent = 'Proof.';
    const errorString = 'illegal begin of vernac';
    const bp = 5;
    const ep = 6;

    let duringPromise = Promise.resolve();

    worker.addExpectedCall(`${content}`, [
      'Ack',
      '(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
      `(bol_pos_last 0)(bp ${bp})(ep ${ep})))()(Backtrace())` +
      `(Stream.Error"${errorString}"))`,
      'Completed',
    ], async () => {
      duringPromise = proc.setContent(secondContent);
    });

    worker.addExpectedCall(`"${secondContent}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      'Completed',
    ]);

    await proc.setContent(content);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(2);
    expect(proc.currentContent).to.equal(secondContent);

    expect(proc.state.sentenceSize()).to.equal(1);
    expect(editor.setContentError.callCount).to.equal(1);
    expect(editor.setContentError.lastCall.args[0]).to.include({
      message: errorString,
      beginIndex: bp,
      endIndex: ep,
    });

    expect(editor.setContentSuccess.callCount).to.be.equal(1);
  });


  it('should handle no content', async () => {
    await proc.setContent('');
    expect(worker.getCallAmount()).to.equal(0);

    expect(editor.setContentSuccess.callCount).to.equal(0);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(proc.state.sentenceSize()).to.equal(0);
  });

  it('should handle just whitespace content', async () => {
    await proc.setContent(' ');
    expect(worker.getCallAmount()).to.equal(0);

    expect(editor.setContentSuccess.callCount).to.equal(1);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(proc.state.sentenceSize()).to.equal(0);
  });

  it('should handle just whitespace content changes', async () => {
    await proc.setContent(' ');
    await proc.setContent('  ');
    expect(worker.getCallAmount()).to.equal(0);

    expect(editor.setContentSuccess.callCount).to.equal(2);
    expect(editor.setContentError.callCount).to.equal(0);

    expect(proc.state.sentenceSize()).to.equal(0);
  });
});
