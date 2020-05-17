import Notebook from '../../../src/io/notebook';
import {COQ_SPECIAL_COMMENT_START} from '../../../src/io/notebook';

const fs = require('fs');
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
 * Exports the notebook to a Coq file
 * @param {string} file the desired file path
 * @return {Promise} a promise for Mocha
 */
function exportToCoq(file) {
  return new Promise((resolve, reject) => {
    notebook.exportToCoq(
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
  describe('Export notebook to Coq', () => {
    before(() => {
      notebook.filePath = '';
      notebook.blocks = [];
    });

    it('should save Coq code as-is', (done) => {
      const readFile = notebookPath + 'code-block.wpn';
      const writeFile = readFile + '.temp';
      loadNotebook(readFile).then(() => {
        return exportToCoq(writeFile);
      }).then(() => {
        const data = fs.readFileSync(writeFile, 'utf-8');
        fs.unlinkSync(writeFile);
        expect(data).to.include('Lemma a: forall n: nat, n + 0 = n.');
        done();
      }).catch(done);
    });

    it('should save text in a Coq comment', (done) => {
      const readFile = notebookPath + 'text-block.wpn';
      const writeFile = readFile + '.temp';
      loadNotebook(readFile).then(() => {
        return exportToCoq(writeFile);
      }).then(() => {
        const data = fs.readFileSync(writeFile, 'utf-8');
        fs.unlinkSync(writeFile);
        expect(data).to.include(COQ_SPECIAL_COMMENT_START
            + 'This is some sample text.*)');
        done();
      }).catch(done);
    });

    it('should save hints in a Coq comment', (done) => {
      const readFile = notebookPath + 'hint-block.wpn';
      const writeFile = readFile + '.temp';
      loadNotebook(readFile).then(() => {
        return exportToCoq(writeFile);
      }).then(() => {
        const data = fs.readFileSync(writeFile, 'utf-8');
        fs.unlinkSync(writeFile);
        expect(data).to.include(COQ_SPECIAL_COMMENT_START
            + 'It\'s really not that hard.*)');
        done();
      }).catch(done);
    });

    it('should save the start and end of input areas as Coq comments',
        (done) => {
          const readFile = notebookPath + 'input-area.wpn';
          const writeFile = readFile + '.temp';
          loadNotebook(readFile).then(() => {
            return exportToCoq(writeFile);
          }).then(() => {
            const data = fs.readFileSync(writeFile, 'utf-8');
            fs.unlinkSync(writeFile);
            expect(data).to.include(COQ_SPECIAL_COMMENT_START
                + '(* Start of input area *)*)');
            expect(data).to.include(COQ_SPECIAL_COMMENT_START
                + '(* End of input area *)*)');
            done();
          }).catch(done);
        });

    it('should not include Coq comment indicators in text blocks', (done) => {
      const block = {
        type: 'text',
        text: 'There is a (* Coq comment*) in this text block.',
      };

      notebook.exerciseSheet = false;
      notebook.blocks = [block];

      const name = notebookPath + 'save-test.temp';

      exportToCoq(name).then(() => {
        let text = fs.readFileSync(name, 'utf-8');

        fs.unlinkSync(name);
        expect(text).to.startWith('(*');
        expect(text).to.endWith('*) ');
        text = text.slice(2, text.length - 3);
        expect(text).not.to.include('(*');
        expect(text).not.to.include('*)');
        done();
      }).catch(done);
    });
  });
}
