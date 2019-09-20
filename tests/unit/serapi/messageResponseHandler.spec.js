import SerapiCommands from '../../../src/coq/serapi/SerapiCommands.js';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('serapi message response handler', () => {
  let serapi;

  beforeEach(() => {
    sandbox.replace(console, 'warn', sinon.fake());

    serapi = new SerapiCommands(null, sinon.fake());
    sandbox.replace(serapi, 'checkType', sinon.fake());
    serapi.ready = true;
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should parse check response', () => {
    const feedback = '(Feedback((doc_id 0)(span_id 1)(route 0)' +
      '(contents(Message Notice()' +
        '(Pp_glue((Pp_glue((Pp_tag constr.reference(Pp_string plus_O_n))' +
        'Pp_force_newline(Pp_string"     : ")))(Pp_box(Pp_hovbox 0)' +
        '(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword' +
        '(Pp_string forall))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)(Pp_glue(' +
        '(Pp_string n)(Pp_string" : ")(Pp_tag constr.reference(Pp_string nat' +
        '))))))))(Pp_string ,)(Pp_print_break 1 0)(Pp_box(Pp_hovbox 0)' +
        '(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue((Pp_string 0)' +
        '(Pp_tag constr.notation(Pp_string" +"))(Pp_print_break 1 0)' +
        '(Pp_tag constr.variable(Pp_string n)))))(Pp_tagconstr.notation' +
        '(Pp_string" ="))(Pp_print_break 1 0)' +
        '(Pp_tag constr.variable(Pp_string n))))))))))))))';
    serapi.handleMessage(feedback);

    const expectedResponse = 'plus_O_n : forall n : nat, 0 + n = n ';
    const response = serapi.messageCallback.lastCall.args[0];
    expect(response).to.be.eql(expectedResponse);
  }),

  it('should parse search response', () => {
    const feedback = '(Feedback((doc_id 0)(span_id 1)(route 0)' +
      '(contents(Message Info()' +
        '(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_glue((Pp_string plus_O_n)' +
        '(Pp_print_break 1 0)(Pp_string" ")))(Pp_box(Pp_hovbox 0)' +
        '(Pp_glue((Pp_box(Pp_hovbox 2)(Pp_glue((Pp_tag constr.keyword' +
        '(Pp_string forall))(Pp_print_break 1 0)(Pp_box(Pp_hovbox 1)' +
        '(Pp_glue((Pp_string n)(Pp_string" : ")(Pp_tag constr.reference' +
        '(Pp_string nat))))))))(Pp_string ,)(Pp_print_break 1 0)' +
        '(Pp_box(Pp_hovbox 0)(Pp_glue((Pp_box(Pp_hovbox 0)(Pp_glue(' +
        '(Pp_string 0)(Pp_tag constr.notation(Pp_string" +"))' +
        '(Pp_print_break 1 0)(Pp_tag constr.variable(Pp_string n)))))' +
        '(Pp_tagconstr.notation(Pp_string" ="))(Pp_print_break 1 0)' +
        '(Pp_tag constr.variable(Pp_string n)))))))))))Pp_force_newline))))))';
    serapi.handleMessage(feedback);

    const expectedResponse = 'plus_O_n forall n : nat, 0 + n = n ';
    const response = serapi.messageCallback.lastCall.args[0];
    expect(response).to.be.eql(expectedResponse);
  });

  const testClassify = function(parsedData, name, content, object) {
    serapi.currentTag = 'check-' + name + '-0';
    const expectedResponse = {
      name: name,
      content: content,
      objectName: object,
      isLemma: object === 'Lemma',
    };
    const original = {
      name: name,
      content: content,
      objectName: '',
      isLemma: null,
    };

    const onSuccess = () => {};
    const onResult = () => {};

    serapi.callbacks.set(serapi.currentTag, {onResult, onSuccess});
    serapi.searchResults.set(name, original);
    serapi.handleCheckFeedback(parsedData);
    expect(original).to.be.eql(expectedResponse);
    expect(serapi.searchResults.size).to.be.eql(0);
  };

  it('should classify lemmas correctly', () => {
    const parsedData = 'forall n : nat, 0 + n = n : Prop ';
    const name = 'plus_O_n';
    const content = 'forall n : nat, 0 + n = n';
    testClassify(parsedData, name, content, 'Lemma');
  });

  it('should classify definitions correctly', () => {
    const parsedData = 'nat -> nat -> nat : Set ';
    const name = 'Nat.add';
    const content = 'nat -> nat -> nat';
    testClassify(parsedData, name, content, 'Definition');
  });

  it('should extract correct name and content from search feedback', () => {
    const parsedData = 'and_comm forall A B : Prop, A /\\ B <-> B /\\ A ';
    const expectedName = 'and_comm';
    const expectedContent = 'forall A B : Prop, A /\\ B <-> B /\\ A';

    serapi.currentTag = 'search-0';
    serapi.callbacks.set(serapi.currentTag, {onResult: () => {}});
    serapi.handleSearchFeedback(parsedData);
    const result = serapi.searchResults.get(expectedName);
    expect(result.name).to.be.eql(expectedName);
    expect(result.content).to.be.eql(expectedContent);
  });

  it('should fail on an error result from search feedback', () => {
    const parsedData = 'Error: This does not exists';

    serapi.currentTag = 'search-0';
    serapi.callbacks.set(serapi.currentTag, {onResult: () => {}});
    expect(serapi.searchesCompleted).to.equal(0);
    serapi.handleSearchFeedback(parsedData);
    expect(serapi.searchResults.has('Error')).to.equal(false);
    expect(serapi.searchResults.has('Error:')).to.equal(false);
    expect(serapi.searchesCompleted).to.equal(1);
  });

  it('should remove any : from name', () => {
    const parsedData = 'and_comm: forall A B : Prop, A /\\ B <-> B /\\ A ';
    const expectedName = 'and_comm';
    const expectedContent = 'forall A B : Prop, A /\\ B <-> B /\\ A';

    serapi.currentTag = 'search-0';
    serapi.callbacks.set(serapi.currentTag, {onResult: () => {}});
    serapi.handleSearchFeedback(parsedData);
    const result = serapi.searchResults.get(expectedName);
    expect(result.name).to.be.eql(expectedName);
    expect(result.content).to.be.eql(expectedContent);
  });

  it('should ignore results with ?', () => {
    const parsedData = 'name_with? should not be here';

    serapi.currentTag = 'search-0';
    serapi.callbacks.set(serapi.currentTag, {onResult: () => {}});
    expect(serapi.searchesCompleted).to.equal(0);
    serapi.handleSearchFeedback(parsedData);
    expect(serapi.searchResults.has('name_with?')).to.equal(false);
    expect(serapi.searchResults.has('name_with')).to.equal(false);
    expect(serapi.searchesCompleted).to.equal(1);
  });
});
