import Notebook from '../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;
const notebook = new Notebook;


describe('Parse coq to code and text', () => {
  it('should give just one code block if there are no comments',
      (done) => {
        const input = 'Lemma trans (A B C :Prop): ' +
          '(A -> B) -> (B->C) -> A -> C.\n' +
          'Proof.\n' +
          'intro H.\n' +
          'intro G.\n' +
          'intro a.\n' +
          'specialize (H a).\n' +
          'specialize (G H).\n' +
          'apply G.\n' +
          'Qed.';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[0]).to.have.property('text', input);
        done();
      });

  it('should give just one text block if there are only comments',
      (done) => {
        const input = '(* Just a comment *)';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'text');
        done();
      });

  it('should give one text and one code block with code first',
      (done) => {
        const code = 'Lemma trans (A B C :Prop): (A -> B) -> (B->C) -> A -> C.';
        const comment = ' Just a comment ';

        const input = code + '(*' + comment + '*)';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(2);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('type', 'text');
        expect(blocks[1]).to.have.property('text', comment);
        done();
      });

  it('should give one text and one code block with text first',
      (done) => {
        const code = 'Lemma trans (A B C :Prop): (A -> B) -> (B->C) -> A -> C.';
        const comment = ' Just a comment ';

        const input = '(*' + comment + '*)' + code;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(2);
        expect(blocks[0]).to.have.property('type', 'text');
        expect(blocks[0]).to.have.property('text', comment);
        expect(blocks[1]).to.have.property('type', 'code');
        done();
      });

  it('should give one text and two code blocks with text in the middle',
      (done) => {
        const code = 'Lemma trans (A B C :Prop): (A -> B) -> (B->C) -> A -> C.';
        const comment = ' Just a comment ';

        const input = code + '(*' + comment + '*)' + code;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(3);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('type', 'text');
        expect(blocks[2]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('text', comment);
        done();
      });

  it('should give one text block with nested comments',
      (done) => {
        const comment = '(* Just a comment *)';

        const input = '(*' + comment + '*)';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'text');
        expect(blocks[0]).to.have.property('text', comment);
        done();
      });

  it('should give one text block for non closed comment',
      (done) => {
        const comment = ' Just a comment ';

        const input = '(*' + comment;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'text');
        expect(blocks[0]).to.have.property('text', comment);
        done();
      });

  it('should give one text block after a code block for non closed comment',
      (done) => {
        const code = 'Lemma trans (A B C :Prop): (A -> B) -> (B->C) -> A -> C.';
        const comment = ' Just a comment ';

        const input = code + '(*' + comment;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(2);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('type', 'text');
        expect(blocks[1]).to.have.property('text', comment);
        done();
      });

  it('should give one text block non closed comment with nesting',
      (done) => {
        const code = 'Lemma trans (A B C :Prop): (A -> B) -> (B->C) -> A -> C.';
        const comment = ' Just a comment (* Nested comment *)';

        const input = code + ' (*' + comment;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(2);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('type', 'text');
        expect(blocks[1]).to.have.property('text', comment);
        done();
      });

  it('should not revert exported comments "( *", "* )" in comments',
      (done) => {
        // export -> import does not need to give the same result
        const comment = ' Just a comment ( * Nested comment * )';

        const input = '(*' + comment + '*)';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'text');
        expect(blocks[0]).to.have.property('text', comment);
        done();
      });
});
