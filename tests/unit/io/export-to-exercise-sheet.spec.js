import Notebook from '../../../src/io/notebook';

const chai = require('chai');
chai.use(require('chai-string'));
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

/**
 * Exports the notebook to an exercise sheet
 * @param {string} file the desired file path
 * @return {Promise} a promise for Mocha
 */
function exportToExerciseSheet(file) {
  return new Promise((resolve, reject) => {
    notebook.exportToExerciseSheet(
        file,
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
  describe('Export notebook to exercise sheet', () => {
    before(() => {
      notebook.filePath = '';
      notebook.blocks = [];
    });

    it('should properly export a file containing text', (done) => {
      const readFile = notebookPath + 'text-block.wpn';
      const writeFile = readFile + '.temp';
      const expected = {
        type: 'text',
        text: 'This is some sample text.',
      };

      loadNotebook(readFile).then(() => {
        return exportToExerciseSheet(writeFile);
      }).then(() => {
        loadNotebook(writeFile).then(() => {
          expect(notebook.blocks).to.have.lengthOf(1);
          expect(notebook.blocks[0]).to.deep.include(expected);
          chai.assert(notebook.exerciseSheet);
          done();
        });
      }).catch(done);
    });

    it('should properly export a file containing code', (done) => {
      const readFile = notebookPath + 'code-block.wpn';
      const writeFile = readFile + '.temp';
      const expected = {
        type: 'code',
        text: 'Lemma a: forall n: nat, n + 0 = n.',
      };

      loadNotebook(readFile).then(() => {
        return exportToExerciseSheet(writeFile);
      }).then(() => {
        loadNotebook(writeFile).then(() => {
          expect(notebook.blocks).to.have.lengthOf(1);
          expect(notebook.blocks[0]).to.deep.include(expected);
          chai.assert(notebook.exerciseSheet);
          done();
        });
      }).catch(done);
    });

    it('should properly export a file containing a hint', (done) => {
      const readFile = notebookPath + 'hint-block.wpn';
      const writeFile = readFile + '.temp';
      const expected = {
        type: 'hint',
        text: 'It\'s really not that hard.',
      };

      loadNotebook(readFile).then(() => {
        return exportToExerciseSheet(writeFile);
      }).then(() => {
        loadNotebook(writeFile).then(() => {
          expect(notebook.blocks).to.have.lengthOf(1);
          expect(notebook.blocks[0]).to.deep.include(expected);
          chai.assert(notebook.exerciseSheet);
          done();
        });
      }).catch(done);
    });

    it('should not make the current notebook an exercise sheet', (done) => {
      const readFile = notebookPath + 'code-block.wpn';
      const writeFile = readFile + '.temp';

      loadNotebook(readFile).then(() => {
        return exportToExerciseSheet(writeFile);
      }).then(() => {
        chai.assert(!notebook.exerciseSheet);
        done();
      }).catch(done);
    });
  });
}
