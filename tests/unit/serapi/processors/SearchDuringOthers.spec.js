// import SerapiContentProcessor
//   from '../../../../src/coq/serapi/processors/SerapiContentProcessor';
// import SerapiExecutionProcessor
//   from '../../../../src/coq/serapi/processors/SerapiExecutionProcessor';
// import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
// import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
// import EditorInterface from '../../../../src/coq/EditorInterface';
//
// import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
// import SerapiSearchProcessor
//   from '../../../../src/coq/serapi/processors/SerapiSearchProcessor';
//
// const chai = require('chai');
// const expect = chai.expect;
// const sinon = require('sinon');
//
// describe('serapi combined content & execution processor', () => {
//   let contentProc;
//   let execProc;
//   let searchProc;
//
//   let worker;
//   const editor = new EditorInterface();
//
//   beforeEach(() => {
//     worker = new ExpectingSerapiWorker();
//
//     sinon.spy(editor, 'setContentSuccess');
//     sinon.spy(editor, 'setContentError');
//     sinon.spy(editor, 'executeStarted');
//     sinon.spy(editor, 'executeSuccess');
//     sinon.spy(editor, 'executeError');
//
//     const tagger = new SerapiTagger(worker, () => {
//     });
//     const state = new SerapiState();
//
//     contentProc = new SerapiContentProcessor(tagger, state, editor);
//
//     execProc = new SerapiExecutionProcessor(tagger, state, editor);
//
//     searchProc = new SerapiSearchProcessor(tagger, state, editor);
//   });
//
//   afterEach(() => {
//     sinon.restore();
//   });
// });
