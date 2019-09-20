import Notebook from '../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;
const notebook = new Notebook;

// The path to the test notebooks, relative to the `io` source folder
const notebookPath = './tests/unit/io/test-notebooks/';

/**
 * Loads the specified notebook
 * @param {string} file the desired test notebook
 * @return {Promise} a promise that resolves when the file is read,
 *    or rejects when a read or parse error occurs
 */
function loadNotebook(file) {
  notebook.filePath = file;

  return new Promise((resolve, reject) => {
    notebook.read(
        () => {
          resolve();
        },
        (err) => {
          reject(err);
        }
    );
  });
}

if (process.env.NODE_ENV !== 'coverage') {
  describe('Load notebook', () => {
    before(() => {
      notebook.filePath = '';
      notebook.blocks = [];
    });

    it('should load a text block correctly', (done) => {
      const file = notebookPath + 'text-block.wpn';
      const expected = {
        type: 'text',
        text: 'This is some sample text.',
      };

      loadNotebook(file).then(() => {
        expect(notebook.blocks).to.have.lengthOf(1);
        expect(notebook.blocks[0]).to.deep.include(expected);
        done();
      }).catch(done);
    });

    it('should load a code block correctly', (done) => {
      const file = notebookPath + 'code-block.wpn';
      const expected = {
        type: 'code',
        text: 'Lemma a: forall n: nat, n + 0 = n.',
      };

      loadNotebook(file).then(() => {
        expect(notebook.blocks).to.have.lengthOf(1);
        expect(notebook.blocks[0]).to.deep.include(expected);
        done();
      }).catch(done);
    });

    it('should load a hint block correctly', (done) => {
      const file = notebookPath + 'hint-block.wpn';
      const expected = {
        type: 'hint',
        text: 'It\'s really not that hard.',
      };

      loadNotebook(file).then(() => {
        expect(notebook.blocks).to.have.lengthOf(1);
        expect(notebook.blocks[0]).to.deep.include(expected);
        done();
      }).catch(done);
    });

    it('should detect if a notebook is an exercise sheet', (done) => {
      const file = notebookPath + 'exercise-sheet.wpn';

      loadNotebook(file).then(() => {
        chai.assert(notebook.exerciseSheet);
        done();
      }).catch(done);
    });

    it('should detect which blocks are in input fields in a non exercise sheet',
        (done) => {
          const file = notebookPath + 'non-exercise-sheet-input.wpn';

          loadNotebook(file).then(() => {
            chai.assert(!notebook.blocks[0].state.inInputField);
            chai.assert(notebook.blocks[2].state.inInputField);
            chai.assert(notebook.blocks[3].state.inInputField);
            chai.assert(!notebook.blocks[5].state.inInputField);
            done();
          }).catch(done);
        });

    it('should detect which blocks are in input fields in an exercise sheet',
        (done) => {
          const file = notebookPath + 'exercise-sheet-input.wpe';

          loadNotebook(file).then(() => {
            chai.assert(!notebook.blocks[0].state.inInputField);
            chai.assert(notebook.blocks[2].state.inInputField);
            chai.assert(notebook.blocks[3].state.inInputField);
            chai.assert(!notebook.blocks[5].state.inInputField);
            done();
          }).catch(done);
        });
  });
}
