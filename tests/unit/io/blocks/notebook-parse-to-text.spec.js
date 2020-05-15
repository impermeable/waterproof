import Notebook from '../../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;


describe('Notebook parse to text ', () => {
  const notebook = new Notebook;

  beforeEach(() => {
    notebook.clearContent();
  });

  it('should parse to empty string if no blocks in notebook', (done) => {
    const output = notebook.parseToText();
    expect(output).to.have.length(0);

    done();
  });

  it('should parse code block directly', (done) => {
    const code = 'Lemma a n: n+0=n.';
    notebook.blocks.push(
        notebook.createCodeBlock(code, false));
    const output = notebook.parseToText();
    expect(output.trim()).to.equal(code);

    done();
  });

  it('should parse text block to a comment', (done) => {
    const code = 'Lemma a n: n+0=n.';
    notebook.blocks.push(
        notebook.createTextBlock(code, false));
    const output = notebook.parseToText();
    expect(output.trim()).to.equal('(*' + code + '*)');

    done();
  });

  it('should parse hint block to nothing', (done) => {
    const code = 'Lemma a n: n+0=n.';
    notebook.blocks.push(notebook.createHintBlock(code));
    const output = notebook.parseToText();
    expect(output).includes(code);
    expect(output).to.endsWith('\n');

    done();
  });

  it('should parse input blocks to comments with text', (done) => {
    notebook.blocks = notebook.blocks.concat(notebook.createInputArea('1'));
    const output = notebook.parseToText();
    expect(output.trim()).startsWith('(*');
    expect(output.trim()).endsWith('*)');
    expect(output).includes('(* Start of input area *)');
    expect(output).includes('(* End of input area *)');

    done();
  });
});
