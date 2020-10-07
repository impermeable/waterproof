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

const responseWithText = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents(Message Notice()' +
  '(Pp_glue((Pp_tag constr.path(Pp_string Nat))(Pp_string .)(Pp_tag constr.' +
  'reference(Pp_string add))Pp_force_newline(Pp_string"     : ")(Pp_box(Pp_ho' +
  'vbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string nat))(Pp_tag constr.nota' +
  'tion(Pp_string" ->"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_' +
  'tag constr.variable(Pp_string nat))(Pp_tag constr.notation(Pp_string" ->")' +
  ')(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string nat))))))))))))))',
  '(ObjList())',
  'Completed',
];

const errorResponse = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  '(CoqExn((loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last' +
  ` 1)(bol_pos_last 0)(bp 6)(ep 9))))(stm_ids((1 2)))(backtrace(` +
  'Backtrace()))(exn("Nametab.GlobalizationError(_)"))(pp(Pp_glue' +
  '((Pp_glue())(Pp_glue((Pp_glue((Pp_glue((Pp_string"The reference")(' +
  'Pp_print_break 1 0)(Pp_string b)))(Pp_print_break 1 0)(' +
  'Pp_string"was not found")))(Pp_print_break 1 0)(Pp_string"in the ' +
  'current")))(Pp_print_break 1 0)(Pp_string environment.))))' +
  `(str"The reference abc was not found in the current environment.")))`,
  'Completed',
];


describe('serapi query processor (part of search)', () => {
  let proc;
  let worker;
  let state;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();
    state = new SerapiState();

    sinon.spy(editor, 'setContentSuccess');
    sinon.spy(editor, 'setContentError');
    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');
    sinon.spy(editor, 'message');

    proc = new SerapiSearchProcessor(
        new SerapiTagger(worker, null),
        state,
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });

  it('should send the vernac with the command', async () => {
    const command = 'Check plus.';
    worker.addExpectedCall(`(Query () (Vernac "${command}"`, emptyResponse);

    await proc.query(command);

    expect(worker.getCallAmount()).to.equal(1);

    expect(editor.message.callCount).to.equal(0);
  });

  it('should send a message through to the editor', async () => {
    const command = 'Check plus.';
    const expectedString = 'Nat.add : nat -> nat -> nat ';
    worker.addExpectedCall(`(Query () (Vernac "${command}"`, responseWithText);

    await proc.query(command);

    expect(worker.getCallAmount()).to.equal(1);

    expect(editor.message.callCount).to.equal(1);
    expect(editor.message.lastCall.args[0]).to.equal(expectedString);
  });

  it('should display the error if one occurred', async () => {
    const command = 'Check abc.';
    const expectedError =
      'The reference abc was not found in the current environment.';
    worker.addExpectedCall(`(Query () (Vernac "${command}"`, errorResponse);

    await proc.query(command);

    expect(worker.getCallAmount()).to.equal(1);

    expect(editor.message.callCount).to.equal(1);
    expect(editor.message.lastCall.args[0]).to.equal(expectedError);
  });

  it('should wait with querying until state lock released', async () => {
    const release = await state.stateLock.acquire();
    let released = false;

    setTimeout(() => {
      released = true;
      release();
    }, 0);

    const command = 'Check plus.';
    const expectedString = 'Nat.add : nat -> nat -> nat ';

    worker.addExpectedCall(`(Query () (Vernac "${command}"`, responseWithText,
        () => {
          expect(released).to.equal(true);
        });

    await proc.query(command);

    expect(worker.getCallAmount()).to.equal(1);

    expect(editor.message.callCount).to.equal(1);
    expect(editor.message.lastCall.args[0]).to.equal(expectedString);
  });
});
