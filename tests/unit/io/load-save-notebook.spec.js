import Notebook from '../../../src/io/notebook';

const fs = require('fs');
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
        },
    );
  });
}

/**
 * Saves the notebook to the correct path
 * @param {string} file desired filename
 * @return {Promise} which resolves on completion of the save, and is
 *      rejected when the save fails
 */
function saveNotebook(file) {
  notebook.filePath = file;
  return new Promise((resolve, reject) => {
    notebook.write(
        () => {
          resolve();
        },
        (err) => {
          reject(err);
        },
    );
  });
}


if (process.env.NODE_ENV !== 'coverage') {
  describe('Save & load notebook', () => {
    /**
     * @param {string} name
     * @param {function} isDone callback to signify the test case is done
     * @return {Promise} a promise for Mocha
     *
     */
    function checkSaveLoad(name, isDone) {
      const readFile = notebookPath + name;
      const writeFile = readFile + '.temp';
      return loadNotebook(readFile).then(() => {
        return saveNotebook(writeFile);
      }).then(() => {
        let data1 = fs.readFileSync(readFile, 'utf-8').trim();
        data1 = data1.replace(/\r/g, '');
        let data2 = fs.readFileSync(writeFile, 'utf-8').trim();
        data2 = data2.replace(/\r/g, '');
        fs.unlinkSync(writeFile);
        expect(data1).to.deep.equal(data2);
        isDone();
      }).catch(isDone);
    }

    before(() => {
      notebook.filePath = '';
      notebook.blocks = [];
    });

    it('should save a loaded text block correctly', (done) => {
      checkSaveLoad('text-block.wpn', () => {
        done();
      });
    });

    it('should save a loaded code block correctly', (done) => {
      checkSaveLoad('code-block.wpn', () => {
        done();
      });
    });

    it('should save a loaded hint block correctly', (done) => {
      checkSaveLoad('hint-block.wpn', () => {
        done();
      });
    });
  });
}
