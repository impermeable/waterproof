import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiASTProcessor
  from '../../../../src/coq/serapi/processors/SerapiASTProcessor';
import {CoqAST} from '../../../../src/coq/serapi/ASTProcessor';

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

describe('serapi ast processor', () => {
  let proc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    proc = new SerapiASTProcessor(
        new SerapiTagger(worker, null),
        new SerapiState(),
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should send the correct command when getting one ast', async () => {
    const id = 3;
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

    worker.addExpectedCall(`(Query ((sid ${id})(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    await proc.getAstForSentence(proc.state.indexOfSentence(id));
    expect(worker.getCallAmount()).to.equal(1);

    expect(proc.state.getASTOfSentence(0)).to.not.be.ok;
    expect(proc.state.getASTOfSentence(1)).to.be.instanceof(CoqAST);
  });


  it('should send a command per sentence if all ast are requested',
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
        ]);

        worker.addExpectedCall(`(Query ((sid 2)(pp ((pp_format PpSer)))) Ast)`,
            proofResponse);

        worker.addExpectedCall(`(Query ((sid 3)(pp ((pp_format PpSer)))) Ast)`,
            proofResponse);

        await proc.getAllAsts();
        expect(worker.getCallAmount()).to.equal(2);

        expect(proc.state.getASTOfSentence(0)).to.be.instanceOf(CoqAST);
        expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
        expect(proc.state.getASTOfSentence(0)).to.not.equal(
            proc.state.getASTOfSentence(1));
      });

  it('should not run multiple queries (as to not interfere)', async () => {
    const id1 = 2;
    const id2 = 3;
    let duringPromise = Promise.resolve();
    proc.state.concatSentences([
      {
        beginIndex: 0,
        endIndex: 6,
        sentenceId: id1,
      },
      {
        beginIndex: 7,
        endIndex: 13,
        sentenceId: id2,
      },
    ]);

    worker.addExpectedCall(`(Query ((sid ${id1})(pp ((pp_format PpSer)))) Ast)`,
        proofResponse,
        () => {
          duringPromise = proc.getAstForSentence(
              proc.state.indexOfSentence(id2));
        });
    worker.addExpectedCall(`(Query ((sid ${id2})(pp ((pp_format PpSer)))) Ast)`,
        proofResponse);

    await proc.getAstForSentence(proc.state.indexOfSentence(id1));
    await duringPromise;
    expect(worker.getCallAmount()).to.equal(2);

    expect(proc.state.getASTOfSentence(0)).to.be.instanceOf(CoqAST);
    expect(proc.state.getASTOfSentence(1)).to.be.instanceOf(CoqAST);
    expect(proc.state.getASTOfSentence(0)).to.not.equal(
        proc.state.getASTOfSentence(1));
  });
});
