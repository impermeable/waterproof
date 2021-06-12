import Notebook from '../../../src/io/notebook';

const fs = require('fs');
const chai = require('chai');
const expect = chai.expect;
const notebook = new Notebook;

// The path to the test notebooks, relative to the `io` source folder
const notebookPath = './tests/unit/io/test-notebooks/';

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
  describe('Save notebook', () => {
    before(() => {
      notebook.filePath = '';
      notebook.commandBlacklist = new Set(),
      notebook.blocks = [];
      notebook.exerciseSheet = false;
    });

    it('should save a code block properly', (done) => {
      const content = [
        {
          type: 'code',
          text: 'Lemma a: forall n: nat, n + 0 = n.',
          state: {
            error: null,
            done: false,
          },
        },
      ];

      notebook.blocks = content;
      const name = notebookPath + 'save-test.temp';

      saveNotebook(name).then(() => {
        const obj = JSON.parse(fs.readFileSync(name));

        // Retain only the type and text attributes
        const full = content[0];
        content[0] = {type: full.type, text: full.text};

        fs.unlinkSync(name);
        expect(obj).to.deep.equal({
          blocks: content,
          exerciseSheet: false,
        });
        done();
      }).catch(done);
    });

    it('should save a text block properly', (done) => {
      const content = [
        {
          type: 'text',
          text: 'This is some sample text.',
        },
      ];

      notebook.blocks = content;
      const name = notebookPath + 'save-test.temp';

      saveNotebook(name).then(() => {
        const obj = JSON.parse(fs.readFileSync(name));

        fs.unlinkSync(name);
        expect(obj).to.deep.equal({
          blocks: content,
          exerciseSheet: false,
        });
        done();
      }).catch(done);
    });

    it('should save a hint block properly', (done) => {
      const content = [
        {
          type: 'hint',
          text: 'Try solving the exercises.',
        },
      ];

      notebook.blocks = content;
      const name = notebookPath + 'save-test.temp';

      saveNotebook(name).then(() => {
        const obj = JSON.parse(fs.readFileSync(name));

        fs.unlinkSync(name);
        expect(obj).to.deep.equal({
          blocks: content,
          exerciseSheet: false,
        });
        done();
      }).catch(done);
    });

    it('should save the command blacklist properly', (done) => {
      const commandBlacklist = new Set(['Admitted.', 'Axiom', 'Pattern']);
      notebook.commandBlacklist = commandBlacklist;
      notebook.exerciseSheet = true;
      const name = notebookPath + 'save-test.temp';
      saveNotebook(name).then(() => {
        const obj = JSON.parse(fs.readFileSync(name));
        const readBlacklist = new Set(obj.commandBlacklist);
        expect(readBlacklist).to.deep.equal(commandBlacklist);

        fs.unlinkSync(name);
        done();
      }).catch(done);
    });

    it('should include Coq comment indicators in text blocks', (done) => {
      const block = {
        type: 'text',
        text: 'There is a (* Coq comment*) in this text block.',
      };

      notebook.exerciseSheet = false;
      notebook.blocks = [block];

      const name = notebookPath + 'save-test.temp';

      saveNotebook(name).then(() => {
        const text = fs.readFileSync(name, 'utf-8');

        fs.unlinkSync(name);
        expect(text).to.include('(*');
        expect(text).to.include('*)');
        done();
      }).catch(done);
    });
  });
}
