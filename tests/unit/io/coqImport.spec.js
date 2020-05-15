import Notebook from '../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;
const notebook = new Notebook;

describe('Cut code before keywords', () => {
  it('should return empty list for empty string', (done) => {
    const input = '';
    const pieces = notebook.cutStringBetweenKeywords(input);

    expect(pieces).to.eql([]);
    done();
  });

  it('should cut before keywords',
      (done) => {
        const lemmaStatement = 'Lemma trans (A B C :Prop): ' +
          '(A -> B) -> (B->C) -> A -> C.\n';
        const lemmaProof = 'Proof.\n' +
          'intro H.\n' +
          'intro G.\n' +
          'intro a.\n' +
          'specialize (H a).\n' +
          'specialize (G H).\n' +
          'apply G.\n' +
          'Qed.\n      ';
        const input = lemmaStatement + lemmaProof;

        const pieces = notebook.cutStringBetweenKeywords(input);

        expect(pieces).to.be.an('array').that.has.lengthOf(2);
        expect(pieces[0]).to.equal(lemmaStatement.trim());
        expect(pieces[1]).to.equal(lemmaProof.trim());
        done();
      });
});

describe('Parse coq to code and text', () => {
  it('should only give a code block for a notation without comments',
      (done) => {
        const input = 'Notation "cv_to" := Un_cv.';

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(1);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[0]).to.have.property('text', input);
        done();
      });

  it('should split to different code cells before keywords',
      (done) => {
        const lemmaStatement = 'Lemma trans (A B C :Prop): ' +
          '(A -> B) -> (B->C) -> A -> C.\n';
        const lemmaProof = 'Proof.\n' +
          'intro H.\n' +
          'intro G.\n' +
          'intro a.\n' +
          'specialize (H a).\n' +
          'specialize (G H).\n' +
          'apply G.\n' +
          'Qed.';
        const input = lemmaStatement + lemmaProof;

        const blocks = notebook.coqToCodeAndText(input);

        expect(blocks).to.be.an('array').that.has.lengthOf(2);
        expect(blocks[0]).to.have.property('type', 'code');
        expect(blocks[0]).to.have.property('text', lemmaStatement.trim());
        expect(blocks[1]).to.have.property('type', 'code');
        expect(blocks[1]).to.have.property('text', lemmaProof);
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

  it('should remove all hard returns', (done) => {
    const input =
        'Lemma zero_eq_zero : 0 = 0.\r\nProof.\n\rreflexivity.\n\rQed.';

    const blocks = notebook.coqToCodeAndText(input);

    expect(blocks).to.be.an('array').that.has.lengthOf(2);
    expect(blocks[0].text.indexOf('\r')).to.equal(-1);
    expect(blocks[1].text.indexOf('\r')).to.equal(-1);
    done();
  });
});
