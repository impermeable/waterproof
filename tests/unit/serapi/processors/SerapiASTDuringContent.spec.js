import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiASTProcessor
  from '../../../../src/coq/serapi/processors/SerapiASTProcessor';
import {CoqAST} from '../../../../src/coq/serapi/ASTProcessor';
import SerapiContentProcessor
  from '../../../../src/coq/serapi/processors/SerapiContentProcessor';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

const proofResponse = [
  'Ack',
  '(ObjList((CoqAst((v((control())(attrs())(expr(VernacProof()()))))' +
  '(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
  '(bol_pos_last 0)(bp 0)(ep 6))))))))',
  'Completed',
];

describe('serapi ast during content processor', () => {
  let proc;
  let contentProc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    const tagger = new SerapiTagger(worker, null);
    const state = new SerapiState();
    proc = new SerapiASTProcessor(tagger, state, editor);
    contentProc = new SerapiContentProcessor(tagger, state, editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should stop setContent until done (1)', async () => {
    const id = 3;
    let duringPromise = Promise.resolve();
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: 2,
      },
      {
        beginIndex: 7,
        endIndex: 13,
        sentenceId: id,
      },
    ]);

    contentProc.currentContent = 'Proof. Proof.';

    worker.addExpectedCall(`(Query ((sid ${id})(pp ((pp_format PpSer)))) Ast)`,
        proofResponse,
        () => {
          duringPromise = contentProc.setContent('');
        });

    worker.addExpectedCall('Cancel (2 3)', [
      'Ack',
      '(Canceled(2 3))',
      'Completed',
    ],
    );

    await proc.getAstForSentence(proc.state.indexOfSentence(id));
    expect(proc.state.getASTOfSentence(0)).to.not.be.ok;
    expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(2);
    expect(proc.state.sentenceSize()).to.equal(0);
  });

  it('should wait for setContent before asking for asts (1)', async () => {
    const id = 290;
    let duringPromise = Promise.resolve();

    const content = 'Proof. Proof.';
    worker.addExpectedCall(`Add () "${content}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      `(Added ${id}((fname ToplevelInput)(line_nb 1)(bol_pos 0)` +
      '(line_nb_last 1)(bol_pos_last 0)(bp 7)(ep 13))NewTip)',
      'Completed',
    ], () => {
      duringPromise = proc.getAstForSentence(1);
    });

    worker.addExpectedCall(`(Query ((sid ${id})(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    await contentProc.setContent(content);
    expect(proc.state.sentenceSize()).to.equal(2);
    expect(proc.state.getASTOfSentence(0)).to.not.be.ok;
    expect(proc.state.getASTOfSentence(1)).to.not.be.ok;
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(2);

    expect(proc.state.getASTOfSentence(0)).to.not.be.ok;
    expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
  });

  it('should stop setContent until done (all)', async () => {
    let duringPromise = Promise.resolve();
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
    ]);

    contentProc.currentContent = 'Proof. Proof.';

    worker.addExpectedCall(`(Query ((sid 2)(pp ((pp_format PpSer)))) Ast)`,
        proofResponse,
        () => {
          duringPromise = contentProc.setContent('');
        });

    worker.addExpectedCall(`(Query ((sid 3)(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    worker.addExpectedCall('Cancel (2 3)', [
      'Ack',
      '(Canceled(2 3))',
      'Completed',
    ]);

    await proc.getAllAsts();
    expect(proc.state.getASTOfSentence(0)).to.be.instanceOf(CoqAST);
    expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(3);
    expect(proc.state.sentenceSize()).to.equal(0);
  });

  it('should wait for setContent before asking for asts (all)', async () => {
    let duringPromise = Promise.resolve();

    const content = 'Proof. Proof.';
    worker.addExpectedCall(`Add () "${content}"`, [
      'Ack',
      '(Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 6))NewTip)',
      '(Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)' +
      '(line_nb_last 1)(bol_pos_last 0)(bp 7)(ep 13))NewTip)',
      'Completed',
    ], () => {
      duringPromise = proc.getAllAsts();
    });

    worker.addExpectedCall(`(Query ((sid 2)(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    worker.addExpectedCall(`(Query ((sid 3)(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    await contentProc.setContent(content);
    expect(proc.state.sentenceSize()).to.equal(2);
    expect(proc.state.getASTOfSentence(0)).to.not.be.ok;
    expect(proc.state.getASTOfSentence(1)).to.not.be.ok;
    await duringPromise;

    expect(worker.getCallAmount()).to.equal(3);

    expect(proc.state.getASTOfSentence(0)).to.be.instanceOf(CoqAST);
    expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
    expect(proc.state.getASTOfSentence(0)).to.not.equal(
        proc.state.getASTOfSentence(1));
  });
});
