import Notebook from '../../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;


describe('Notebook file path', () => {
  let notebook;

  beforeEach(() => {
    notebook = new Notebook;
  });

  it('should not have file path at the start', (done) => {
    expect(notebook.filePath).to.equal('');
    expect(notebook.getName()).to.equal('untitled');
    done();
  });

  it('should update the filepath and name when set', (done) => {
    const filePath = '/test/a/real/path/notebook.wpn';
    notebook.setFilePath(filePath);
    expect(notebook.filePath).to.equal(filePath);
    expect(notebook.getName()).to.equal('notebook.wpn');
    done();
  });
});
