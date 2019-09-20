import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';
import {parseErrorResponse} from '../../../src/coq/serapi/SerapiParser';
import SerapiWorker from '../../../src/coq/serapi/workers/SerapiWorker';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi message handler', () => {
  let serapi;

  beforeEach(() => {
    serapi = new SerapiCommands(null, () => { }, () => { });
    serapi.ready = true;

    sandbox.replace(serapi, 'handleAddResponse', sinon.fake());
    sandbox.replace(serapi, 'handleExecuteResponse', sinon.fake());
    sandbox.replace(serapi, 'handleCancelResponse', sinon.fake());
    sandbox.replace(serapi, 'handleGoalsResponse', sinon.fake());
    sandbox.replace(serapi, 'messageCallback', sinon.fake());

    sandbox.replace(console, 'warn', sinon.fake());
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should set isReady when the correct message is received', (done) => {
    // Tell serapi that it isn't ready yet
    serapi.ready = false;
    const readyMsg = '(Feedback((doc_id 0)(span_id 1)' +
        '(route 0)(contents Processed)))';
    serapi.handleMessage(readyMsg);

    // Should now be ready
    expect(serapi.isReady()).to.be.equal(true);

    // Should not call any other handle methods
    expect(serapi.handleAddResponse.callCount).to.be.equal(0);
    expect(serapi.handleExecuteResponse.callCount).to.be.equal(0);
    expect(serapi.handleCancelResponse.callCount).to.be.equal(0);
    expect(serapi.handleGoalsResponse.callCount).to.be.equal(0);
    done();
  });

  it('should terminate the worker when terminating the serapi commands',
      (done) => {
        const worker = new SerapiWorker;
        sandbox.replace(worker, 'terminate', sinon.fake());
        const newSerapi = new SerapiCommands(worker, () => { }, () => { });

        newSerapi.terminate();

        expect(worker.terminate.callCount).to.equal(1);
        done();
      });

  it('should send answers with an add tag to handleAddResponse', (done) => {
    // (Answer add-42  Ack)
    // (Answer add-42 (Added 2((fname ToplevelInput)(line_nb 1)(bol_pos 0)
    //                   (line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 34))NewTip))
    // (Answer add-42 (Added 3((fname ToplevelInput)(line_nb 1)(bol_pos 0)
    //                  (line_nb_last 1)(bol_pos_last 0)(bp 35)(ep 41))NewTip))
    // (Answer add-42  Completed)
    const msg = '(Answer add-42  Ack)';
    serapi.callbacks.set('add-42', [sinon.fake(), sinon.fake()]);
    serapi.handleMessage(msg);

    // Should call handleAddResponse exactly once
    expect(serapi.handleAddResponse.callCount).to.be.equal(1);
    expect(serapi.handleExecuteResponse.callCount).to.be.equal(0);
    expect(serapi.handleCancelResponse.callCount).to.be.equal(0);
    expect(serapi.handleGoalsResponse.callCount).to.be.equal(0);
    expect(console.warn.callCount).to.be.equal(0);

    done();
  });

  it('should send answers with a cancel tag to handleCancelResponse',
      (done) => {
        const msg = '(Answer cancel-42  Ack)';
        serapi.callbacks.set('cancel-42', [sinon.fake(), sinon.fake()]);
        serapi.handleMessage(msg);

        // Should call handleAddResponse exactly once
        expect(serapi.handleAddResponse.callCount).to.be.equal(0);
        expect(serapi.handleExecuteResponse.callCount).to.be.equal(0);
        expect(serapi.handleCancelResponse.callCount).to.be.equal(1);
        expect(serapi.handleGoalsResponse.callCount).to.be.equal(0);
        expect(console.warn.callCount).to.be.equal(0);

        done();
      });


  it('should send answers with an execute tag to handleExecuteResponse',
      (done) => {
        const msg = '(Answer exec-42  Ack)';
        serapi.callbacks.set('exec-42', [sinon.fake(), sinon.fake()]);
        serapi.handleMessage(msg);

        // Should call handleAddResponse exactly once
        expect(serapi.handleAddResponse.callCount).to.be.equal(0);
        expect(serapi.handleExecuteResponse.callCount).to.be.equal(1);
        expect(serapi.handleCancelResponse.callCount).to.be.equal(0);
        expect(serapi.handleGoalsResponse.callCount).to.be.equal(0);
        expect(console.warn.callCount).to.be.equal(0);

        done();
      });

  it('should send answers with a goals tag to handleGoalsResponse', (done) => {
    const msg = '(Answer goals-42  Ack)';
    serapi.callbacks.set('goals-42', [sinon.fake(), sinon.fake()]);
    serapi.handleMessage(msg);

    // Should call handleAddResponse exactly once
    expect(serapi.handleAddResponse.callCount).to.be.equal(0);
    expect(serapi.handleExecuteResponse.callCount).to.be.equal(0);
    expect(serapi.handleCancelResponse.callCount).to.be.equal(0);
    expect(serapi.handleGoalsResponse.callCount).to.be.equal(1);
    expect(console.warn.callCount).to.be.equal(0);

    done();
  });

  it('should print a warning when receiving a message with unknown tag',
      (done) => {
        const msg = '(Answer add-42  Ack)';
        serapi.callbacks.set('add-24', [sinon.fake(), sinon.fake()]);
        serapi.handleMessage(msg);

        // Should call handleAddResponse exactly once
        expect(serapi.handleAddResponse.callCount).to.be.equal(0);
        expect(serapi.handleExecuteResponse.callCount).to.be.equal(0);
        expect(serapi.handleCancelResponse.callCount).to.be.equal(0);
        expect(serapi.handleGoalsResponse.callCount).to.be.equal(0);
        expect(console.warn.callCount).to.be.equal(1);

        done();
      });


  it('should delete callback functions when the answer is completed',
      (done) => {
        serapi.callbacks.set('add-42', [sinon.fake(), sinon.fake()]);
        const msg = '(Answer add-42 Completed)';
        serapi.handleMessage(msg);
        expect(serapi.callbacks.has('add-42')).to.be.equal(false);


        done();
      });

  it('should process feedback from a check-statement properly', (done) => {
    // eslint-disable-next-line max-len
    const msg = '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message Notice()(Pp_glue((Pp_glue((Pp_tag constr.reference(Pp_string plus_O_n))Pp_force_newline(Pp_string"     : ")))(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string forall))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string n)(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))))))(Pp_string ,)(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_string 0)(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string n)))))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string n))))))))))))))';
    serapi.handleMessage(msg);
    expect(serapi.messageCallback.callCount).to.be.equal(1);
    const arg = serapi.messageCallback.lastCall.args[0];
    expect(arg.includes('plus_O_n')).to.be.equal(true);
    expect(arg.replace(/ /g, '').includes('foralln:nat,0+n=n'))
        .to.be.equal(true);
    done();
  });

  it('should process feedback from a print-statement properly', (done) => {
    // eslint-disable-next-line max-len
    const msg = '(Feedback((doc_id 0)(span_id 3)(route 0)(contents(Message Notice()(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_glue((Pp_string plus_n_Sm)(Pp_string" = ")(Pp_print_break 0 0)))(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string fun))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_glue((Pp_string n)(Pp_print_break 1 0)(Pp_string m)))(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))))))(Pp_print_break 1 0)(Pp_string =>)))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string nat_ind))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string fun))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string n0)(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))))))(Pp_print_break 1 0)(Pp_string =>)))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))(Pp_string")")))))))))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m))))))))))))))))(Pp_string")"))))))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.reference(Pp_string eq_refl))))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string fun))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_glue((Pp_string"(")(Pp_string n0)(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))(Pp_string")"))))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_glue((Pp_string"(")(Pp_string IHn)(Pp_string" : ")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))(Pp_string")")))))))))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))))))))))))(Pp_string")")))))))(Pp_print_break 1 0)(Pp_string =>)))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string f_equal_nat))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.reference(Pp_string nat))))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.reference(Pp_string S))))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))(Pp_string")")))))))))(Pp_string")"))))))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n0))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m))))))))))(Pp_string")"))))))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string IHn))))))))))(Pp_string")"))))))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string n))))))))))Pp_force_newline(Pp_string"     : ")))(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string forall))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_glue((Pp_string n)(Pp_print_break 1 0)(Pp_string m)))(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))))))(Pp_string ,)(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_string"(")(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))(Pp_string")")))))))))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string n))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.reference(Pp_string S))(Pp_glue((Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string m)))))))))))))))))))Pp_force_newline Pp_force_newline(Pp_box(Pp_vbox 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_glue((Pp_glue((Pp_string"Argument scopes are")(Pp_print_break 1 0)(Pp_string [)))(Pp_string nat_scope)(Pp_print_break 1 0)(Pp_string nat_scope)))(Pp_string ])))))))))))';
    // eslint-disable-next-line max-len
    const expected = 'plus_n_Sm = fun n m : nat => nat_ind ( fun n0 : nat => S ( n0 + m ) = n0 + S m ) eq_refl ( fun ( n0 : nat ) ( IHn : S ( n0 + m ) = n0 + S m ) => f_equal_nat nat S ( S ( n0 + m ) ) ( n0 + S m ) IHn ) n : forall n m : nat , S ( n + m ) = n + S m';
    serapi.handleMessage(msg);
    expect(serapi.messageCallback.callCount).to.be.equal(1);
    const arg = serapi.messageCallback.lastCall.args[0];
    expect(arg.replace(/ /g, '').includes(expected.replace(/ /g, '')))
        .to.be.equal(true);
    done();
  });

  it('should process feedback from an about-statement properly', (done) => {
    // eslint-disable-next-line max-len
    const msg = '(Feedback((doc_id 0)(span_id 2)(route 0)(contents(Message Notice()(Pp_box(Pp_vbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_glue((Pp_string f_equal2_plus)(Pp_string" :")(Pp_print_break 1 0)))(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword(Pp_string forall))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue((Pp_glue((Pp_string x1)(Pp_print_break 1 0)(Pp_string y1)(Pp_print_break 1 0)(Pp_string x2)(Pp_print_break 1 0)(Pp_string y2)))(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat))))))))(Pp_string ,)(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string x1))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string y1)))))(Pp_tag constr.notation(Pp_string" ->"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string x2))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string y2)))))(Pp_tag constr.notation(Pp_string" ->"))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string x1))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string x2)))))(Pp_tag constr.notation(Pp_string" ="))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_tag constr.variable(Pp_string y1))(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string y2))))))))))))))))))))(Pp_print_break 0 0)(Pp_print_break 0 0)(Pp_box(Pp_hovbox 2)(Pp_glue((Pp_glue((Pp_glue((Pp_string"Argument scopes are")(Pp_print_break 1 0)(Pp_string [)))(Pp_string nat_scope)(Pp_print_break 1 0)(Pp_string nat_scope)(Pp_print_break 1 0)(Pp_string nat_scope)(Pp_print_break 1 0)(Pp_string nat_scope)(Pp_print_break 1 0)(Pp_string _)(Pp_print_break 1 0)(Pp_string _)))(Pp_string ]))))(Pp_print_break 0 0)(Pp_glue((Pp_string f_equal2_plus)(Pp_string" is ")(Pp_string transparent)))(Pp_print_break 0 0)(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_string"Expands to: ")(Pp_string Constant)(Pp_print_break 1 0)(Pp_string Coq.Init.Peano.f_equal2_plus)))))))))))';

    // eslint-disable-next-line max-len
    const definition = 'f_equal2_plus : forall x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2';
    // eslint-disable-next-line max-len
    const scopes = 'Argument scopes are [nat_scope nat_scope nat_scope nat_scope _ _]';
    const transparent= 'f_equal2_plus is transparent';
    const expands = 'Expands to: Constant Coq.Init.Peano.f_equal2_plus';

    serapi.handleMessage(msg);
    expect(serapi.messageCallback.callCount).to.be.equal(1);

    const arg = serapi.messageCallback.lastCall.args[0].replace(/ /g, '');
    expect(arg.includes(definition.replace(/ /g, ''))).to.be.equal(true);
    expect(arg.includes(scopes.replace(/ /g, ''))).to.be.equal(true);
    expect(arg.includes(transparent.replace(/ /g, ''))).to.be.equal(true);
    expect(arg.includes(expands.replace(/ /g, ''))).to.be.equal(true);
    done();
  });
});

describe('serapi error message handler', () => {
  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should parse additional "Qed."-error', (done) => {
    const msg = ['CoqExn', [], [['15', '0']],
      ['Backtrace', []], 'NoCurrentProof'];
    const parsed = parseErrorResponse(msg);
    expect(parsed.message).to.include('NoCurrentProof');
    expect(parsed.lastCorrectSentence).to.equal(15);
    expect(parsed.failureAtSentence).to.equal(0);
    done();
  });

  it('should parse error for unknown variable', (done) => {
    const msg = ['CoqExn',
      [[['fname', 'ToplevelInput'], ['line_nb', '6'],
        ['bol_pos', '93'], ['line_nb_last', '6'],
        ['bol_post_last', '93'], ['bp', '107'],
        ['ep', '108']]],
      [['6', '7']],
      ['Backtrace', []], ['ExplainErr.EvaluatedError',
        'Ltac call to "specialize (constr_with_bindings)" failed.',
        ['ExplainErr.EvaluatedError',
          'The reference b was not found in the current environment.']]];
    const parsed = parseErrorResponse(msg);
    expect(parsed.message).to.include(
        'The reference b was not found in the current environment'
    );
    expect(parsed.message).not.to.include(
        'Ltac call to "specialize (constr_with_bindings)" failed.'
    );
    expect(parsed.lastCorrectSentence).to.equal(6);
    expect(parsed.failureAtSentence).to.equal(7);
    expect(parsed.beginIndex).to.equal(107);
    expect(parsed.endIndex).to.equal(108);
    done();
  });

  it('should parse error for wrong lemma declaration', (done) => {
    const msg = ['CoqExn',
      [[['fname', 'ToplevelInput'], ['line_nb', '1'],
        ['bol_pos', '0'], ['line_nb_last', '1'],
        ['bol_post_last', '0'], ['bp', '31'],
        ['ep', '33']]],
      [],
      ['Backtrace', []], ['Stream.Error',
        '":=" or ":" or [Prim.name] expected after [Prim.name] ' +
        '(in [constr:closed_binder])']];
    const parsed = parseErrorResponse(msg);
    expect(parsed.message).to.include('expected after');
    expect(parsed.beginIndex).to.equal(31);
    expect(parsed.endIndex).to.equal(33);
    done();
  });

  it('should parse error for Qed before proof finished', (done) => {
    const msg = ['CoqExn', [], [['3', '4']], ['Backtrace', []],
      ['CErrors.UserError',
        ['last tactic before Qed', 'Attempt to save an incomplete proof']]];
    // TODO what should be the correct output here?
    // right now it is:
    // 'last tactic before Qed,Attempt to save an incomplete proof'
    const parsed = parseErrorResponse(msg);
    expect(parsed.message).to.include('last tactic before Qed');
    expect(parsed.message).to.include('Attempt to save an incomplete proof');
    expect(parsed.lastCorrectSentence).to.equal(3);
    expect(parsed.failureAtSentence).to.equal(4);
    done();
  });

  /* TODO test case for:
    Answer add-0(CoqExn(((fname ToplevelInput)(line_nb 12)
    (bol_pos 256)(line_nb_last 12)
    (bol_pos_last 256)(bp 275)(ep 276)))
    ()(Backtrace())(\"CLexer.Error.E(3)\")))
   */
});

describe('serapi basic messages sending', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should send a query message', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const coqQuery = 'Search plus.';
    serapi.query(coqQuery);

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Query');
    expect(serapi.postMessage.lastCall.args[0]).to.include(coqQuery);

    done();
  });

  it('should send a check message', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const name = 'plus';
    const data = 'lemma';
    serapi.checkType(name, data);

    expect(serapi.postMessage.callCount).to.equal(1);
    expect(serapi.postMessage.lastCall.args[0]).to.include('Query');
    expect(serapi.postMessage.lastCall.args[0]).to.include('Check');
    expect(serapi.postMessage.lastCall.args[0]).to.include('Vernac');
    expect(serapi.postMessage.lastCall.args[0]).to.include(data);

    done();
  });

  it('should send three search messages', (done) => {
    sandbox.replace(serapi, 'postMessage', sinon.fake());
    const searchTerm = 'plus';
    serapi.search(searchTerm);

    expect(serapi.postMessage.callCount).to.equal(3);
    for (let i = 0; i < 3; i++) {
      expect(serapi.postMessage.getCall(i).args[0]).includes(searchTerm);
    }

    done();
  });
});

describe('serapi tagging', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should give a different tag the second time', (done) => {
    const firstTag = serapi.nextTagId();
    const secondTag = serapi.nextTagId();

    expect(firstTag).to.not.equal(secondTag);

    done();
  });

  it('should give a different tag the second time', (done) => {
    serapi.currentMessageNumber = Number.MAX_SAFE_INTEGER - 2;
    const firstTag = serapi.nextTagId();
    const secondTag = serapi.nextTagId();
    const thirdTag = serapi.nextTagId();
    const forthTag = serapi.nextTagId();

    expect(firstTag).to.not.equal(secondTag);
    expect(firstTag).to.not.equal(thirdTag);
    expect(firstTag).to.not.equal(forthTag);
    expect(secondTag).to.not.equal(thirdTag);
    expect(secondTag).to.not.equal(forthTag);
    expect(thirdTag).to.not.equal(forthTag);

    done();
  });
});
