import Notebook from '../../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;


describe('Notebook input blocks', () => {
  const notebook = new Notebook;

  it('should create an input block with the correct id and start value',
      (done) => {
        for (let i = -5; i < 5; i++) {
          const startBlock = notebook.createInputBlock(i, true);
          expect(startBlock.id).to.equal(i);
          expect(startBlock.start).to.equal(true);

          const endBlock = notebook.createInputBlock(i, false);
          expect(endBlock.id).to.equal(i);
          expect(endBlock.start).to.equal(false);
        }

        done();
      });

  it('should create both input blocks', (done) => {
    for (let i = -5; i < 5; i++) {
      const blocks = notebook.createInputArea(i);
      expect(blocks).to.be.an('array').that.has.length(2);
      expect(blocks[0].start).to.equal(true);
      expect(blocks[0].id).to.equal(i);
      expect(blocks[1].start).to.equal(false);
      expect(blocks[1].id).to.equal(i);
    }
    done();
  });

  it('should split a start input block correctly', (done) => {
    notebook.blocks = notebook.createInputArea('1');

    const blocks = notebook.splitBlock(0, 0, 0, 'code');
    expect(blocks).to.be.an('array').that.has.length(2);
    expect(blocks[0].type).to.equal('input');
    expect(blocks[0].start).to.equal(true);
    expect(blocks[0].id).to.equal('1');

    expect(blocks[1].type).to.equal('code');
    expect(blocks[1].state.inInputField).to.equal(true);

    notebook.clearContent();

    done();
  });

  it('should split an end input block correctly', (done) => {
    notebook.blocks = notebook.createInputArea('1');

    const blocks = notebook.splitBlock(1, 0, 0, 'code');
    expect(blocks).to.be.an('array').that.has.length(2);
    expect(blocks[0].type).to.equal('code');
    expect(blocks[0].state.inInputField).to.equal(true);

    expect(blocks[1].type).to.equal('input');
    expect(blocks[1].start).to.equal(false);
    expect(blocks[1].id).to.equal('1');

    notebook.clearContent();

    done();
  });
});
