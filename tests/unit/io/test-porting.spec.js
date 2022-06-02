import Notebook from '../../../src/io/notebook';
import {coqToWp} from '../../../src/io/notebook';

const fs = require('fs');
const chai = require('chai');
chai.use(require('chai-string'));
const expect = chai.expect;

const testcasePath = './tests/unit/io/test-porting/';
const tests = ['tutorial', 'block_structure'];

const notebook = new Notebook;


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

function normalizeLineEndings(s) {
  return s.replace(/\r/g, '').replace(/\n/g, '');
}

if (process.env.NODE_ENV !== 'coverage') {
  describe('Full standardized test suite', () => {
    for (let i = 0; i < tests.length; i++) {
      const fname = tests[i];
      it('test ' + fname, (done) => {
        const v = fs.readFileSync(
            testcasePath + fname + '.v', 'utf-8'
        ).toString();
        loadNotebook(testcasePath + fname + '.wpe').then(() => {
          /** EXPORTING */
          const text = notebook.parseToText();
          expect(normalizeLineEndings(text)).to.equal(
              normalizeLineEndings(v)
          );

          /** IMPORTING */
          const blocks = coqToWp(v);
          expect(blocks.length).to.equal(notebook.blocks.length);
          for (let j = 0; j < blocks.length; j++) {
            const a = blocks[j];
            const b = notebook.blocks[j];
            expect(a.type).to.equal(b.type);
            if (b.text !== undefined) {
              expect(normalizeLineEndings(a.text)).to.equal(
                  normalizeLineEndings(b.text.trim())
              );
            }
            expect(a.start).to.equal(b.start);
            //  expect(a.id).to.equal(b.id);
          }
          done();
        }).catch(done);
      });
    }
  });
}
