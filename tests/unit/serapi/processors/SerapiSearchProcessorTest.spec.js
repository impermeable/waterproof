import SerapiState from '../../../../src/coq/serapi/util/SerapiState';
import SerapiTagger from '../../../../src/coq/serapi/SerapiTagger';
import EditorInterface from '../../../../src/coq/EditorInterface';

import ExpectingSerapiWorker from '../util/ExpectingSerapiWorker';
import SerapiSearchProcessor
  from '../../../../src/coq/serapi/processors/SerapiSearchProcessor';

const chai = require('chai');
const expect = chai.expect;
const sinon = require('sinon');

const checkPlusFeedback = '(Feedback((doc_id 0)(span_id 1)(route 0)' +
  '(contents(Message Notice()(Pp_glue((Pp_tag constr.path(Pp_string Nat))' +
  '(Pp_string .)(Pp_tag constr.reference(Pp_string add))Pp_force_newline' +
  '(Pp_string"     : ")(Pp_box(Pp_hovbox 0)' +
  '(Pp_glue((Pp_tag constr.variable(Pp_string nat))' +
  '(Pp_tag constr.notation(Pp_string" ->"))(Pp_print_break 1 0)' +
  '(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string nat))' +
  '(Pp_tag constr.notation(Pp_string" ->"))(Pp_print_break 1 0)' +
  '(Pp_tag constr.variable(Pp_string nat))))))))))))))';

// truncated to 3
const searchPlusFeedbacks = require('./responses/searchPlusResponse');

// truncated to 4 (shares 2 with non quotes)
const searchQuotesPlusFeedbacks =
  require('./responses/searchQuotesPlusResponse');

const emptyResponse = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  '(ObjList())',
  'Completed'];

const errorResponse = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  '(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
  '(bol_pos_last 0)(bp 6)(ep 9)))()(Backtrace())(ExplainErr.EvaluatedError' +
  '"The reference abc was not found in the current environment."))',
  'Completed',
];

const errorWithResultResponse = [
  'Ack',
  '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
  checkPlusFeedback,
  '(CoqExn(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)' +
  '(bol_pos_last 0)(bp 6)(ep 9)))()(Backtrace())(ExplainErr.EvaluatedError' +
  '"The reference abc was not found in the current environment."))',
  'Completed',
];


describe('serapi search processor', () => {
  let proc;
  let worker;
  const editor = new EditorInterface();

  beforeEach(() => {
    worker = new ExpectingSerapiWorker();

    sinon.spy(editor, 'setContentSuccess');
    sinon.spy(editor, 'setContentError');
    sinon.spy(editor, 'executeStarted');
    sinon.spy(editor, 'executeSuccess');
    sinon.spy(editor, 'executeError');

    proc = new SerapiSearchProcessor(
        new SerapiTagger(worker, null),
        new SerapiState(),
        editor);
  });

  afterEach(() => {
    sinon.restore();
  });


  const mapToNameContent = (res) =>
    ({name: res[0].name, content: res[0].content});

  it('should send three commands when searching (no results)', async () => {
    const searchQuery = 'no_results';
    worker.addExpectedCall(`Vernac "Check (${searchQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search (${searchQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${searchQuery}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  async function doAndCheckSecondSearch(firstQuery, secondQuery, firstCalls,
      onDone2, onResult, secondSearch) {
    worker.addExpectedCall(`Vernac "Check (${secondQuery})."`,
        emptyResponse);

    worker.addExpectedCall(`"Search (${secondQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${secondQuery}\\"."`, emptyResponse);

    const onDone1 = sinon.fake();

    await proc.searchFor(firstQuery, onResult, onDone1);
    await secondSearch();

    expect(worker.getCallAmount()).to.equal(firstCalls + 3);

    expect(onDone1.callCount).to.equal(0);
    expect(onDone2.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  }

  it('should cancel the previous search if new search started after call 1',
      async () => {
        const firstQuery = 'no_results';
        const secondQuery = 'second_search_no_results';

        const onResult = sinon.fake();
        const onDone2 = sinon.fake();

        let secondSearch = Promise.resolve();

        worker.addExpectedCall(`Vernac "Check (${firstQuery})."`,
            emptyResponse, async () => {
              secondSearch = proc.searchFor(secondQuery, onResult, onDone2);
            });

        return doAndCheckSecondSearch(firstQuery, secondQuery, 1, onDone2,
            onResult, () => secondSearch);
      });

  it('should cancel the previous search if new search started after call 2',
      async () => {
        const firstQuery = 'no_results';
        const secondQuery = 'second_search_no_results';

        const onResult = sinon.fake();
        const onDone2 = sinon.fake();

        let secondSearch = Promise.resolve();

        worker.addExpectedCall(`Vernac "Check (${firstQuery})."`,
            emptyResponse);

        worker.addExpectedCall(`Search (${firstQuery}).`, emptyResponse,
            async () => {
              secondSearch = proc.searchFor(secondQuery, onResult, onDone2);
            });

        return doAndCheckSecondSearch(firstQuery, secondQuery, 2, onDone2,
            onResult, () => secondSearch);
      });

  it('should cancel the previous search if new search started after call 3',
      async () => {
        const firstQuery = 'no_results';
        const secondQuery = 'second_search_no_results';

        const onResult = sinon.fake();
        const onDone2 = sinon.fake();

        let secondSearch = Promise.resolve();

        worker.addExpectedCall(`Vernac "Check (${firstQuery})."`,
            emptyResponse);

        worker.addExpectedCall(`Search (${firstQuery}).`, emptyResponse);

        worker.addExpectedCall(`Search \\"${firstQuery}\\"`, emptyResponse,
            async () => {
              secondSearch = proc.searchFor(secondQuery, onResult, onDone2);
            });

        return doAndCheckSecondSearch(firstQuery, secondQuery, 3, onDone2,
            onResult, () => secondSearch);
      });

  it('should sanitize the input properly', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        emptyResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should ignore errors, call 1 error', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        errorResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should ignore errors, call 2 error', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        emptyResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, errorResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should ignore errors, call 3 error', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        emptyResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, errorResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should ignore errors, all calls errors', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        errorResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, errorResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, errorResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should ignore results if an error occurred', async () => {
    const searchQuery = '"" \\\\ ""';
    const sanitisedQuery = `\\"\\" \\\\\\\\ \\"\\"`;
    worker.addExpectedCall(`Vernac "Check (${sanitisedQuery})."`,
        errorWithResultResponse);

    worker.addExpectedCall(`"Search (${sanitisedQuery})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${sanitisedQuery}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(searchQuery, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should get results from check', async () => {
    const query = 'plus';
    worker.addExpectedCall(`Check (${query}).`, [
      'Ack',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      checkPlusFeedback,
      '(ObjList())',
      'Completed',
    ]);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(1);

    expect(onResult.lastCall.args[0]).to.include({
      name: 'Nat.add',
      content: 'nat -> nat -> nat',
    });
  });

  it('should get results from search', async () => {
    const query = 'plus';
    worker.addExpectedCall(`Check (${query}).`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, searchPlusFeedbacks);

    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(3);

    expect(onResult.args.map(mapToNameContent)).to.have.deep.members([
      {
        name: 'plus_O_n',
        content: 'forall n : nat, 0 + n = n',
      },
      {
        name: 'plus_n_O',
        content: 'forall n : nat, n = n + 0',
      },
      {
        name: 'mult_n_Sm',
        content: 'forall n m : nat, n * m + n = n * S m',
      },
    ]);
  });

  it('should get results from text search', async () => {
    const query = 'plus';
    worker.addExpectedCall(`Check (${query}).`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);

    worker.addExpectedCall(`"Search \\"${query}\\"."`,
        searchQuotesPlusFeedbacks);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(4);

    expect(onResult.args.map(mapToNameContent)).to.have.deep.members([
      {
        name: 'plus_O_n',
        content: 'forall n : nat, 0 + n = n',
      },
      {
        name: 'plus_n_O',
        content: 'forall n : nat, n = n + 0',
      },
      {
        name: 'plus_n_Sm',
        content: 'forall n m : nat, S (n + m) = n + S m',
      },
      {
        name: 'plus_Sn_m',
        content: 'forall n m : nat, S n + m = S (n + m)',
      },
    ]);
  });

  it('should combine results from all 3 calls without duplicates', async () => {
    const query = 'plus';

    worker.addExpectedCall(`Check (${query}).`, [
      'Ack',
      '(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))',
      checkPlusFeedback,
      '(ObjList())',
      'Completed',
    ]);

    worker.addExpectedCall(`"Search (${query})."`, searchPlusFeedbacks);

    worker.addExpectedCall(`"Search \\"${query}\\"."`,
        searchQuotesPlusFeedbacks);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(6);

    expect(onResult.args.map(mapToNameContent)).to.have.deep.members([
      {
        name: 'Nat.add',
        content: 'nat -> nat -> nat',
      },
      {
        name: 'plus_O_n',
        content: 'forall n : nat, 0 + n = n',
      },
      {
        name: 'plus_n_O',
        content: 'forall n : nat, n = n + 0',
      },
      {
        name: 'mult_n_Sm',
        content: 'forall n m : nat, n * m + n = n * S m',
      },
      {
        name: 'plus_n_Sm',
        content: 'forall n m : nat, S (n + m) = n + S m',
      },
      {
        name: 'plus_Sn_m',
        content: 'forall n m : nat, S n + m = S (n + m)',
      },
    ]);
  });

  it('should ignore results with \'?\'', async () => {
    const query = '_';
    worker.addExpectedCall(`Check (${query}).`,
        require('./responses/checkQuestionMarkResult'));

    worker.addExpectedCall(`"Search (${query})."`, emptyResponse);
    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(0);
  });

  it('should get the correct name even with \':\'', async () => {
    const query = 'add';
    worker.addExpectedCall(`Check (${query}).`, emptyResponse);

    worker.addExpectedCall(`"Search (${query})."`,
        require('./responses/searchAddColonResult'));
    worker.addExpectedCall(`"Search \\"${query}\\"."`, emptyResponse);

    const onResult = sinon.fake();
    const onDone = sinon.fake();

    await proc.searchFor(query, onResult, onDone);

    expect(worker.getCallAmount()).to.equal(3);

    expect(onDone.callCount).to.equal(1);
    expect(onResult.callCount).to.equal(4);

    expect(onResult.args.map((res) => res[0].name)).to.have.members([
      'Nat.tail_add', 'Nat.add', 'Nat.tail_addmul', 'eq_add_S']);
  });
});
