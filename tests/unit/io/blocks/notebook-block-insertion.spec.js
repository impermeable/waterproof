import Notebook from '../../../../src/io/notebook';

const chai = require('chai');
const expect = chai.expect;

const testTypes = ['text', 'code'];

describe('Notebook block insertion', () => {
  it('should give null for an invalid block type', (done) => {
    const notebook = new Notebook;
    const block = notebook.createBlock('invalid type', '');
    expect(block).to.equal(null);
    done();
  });

  testTypes.forEach((type1) => {
    describe(`'${type1}' blocks`, () => {
      const notebook = new Notebook;

      it('should give the right block type when created', (done) => {
        const block = notebook.createBlock(type1, '');
        expect(block.type).to.equal(type1);
        done();
      });

      it('should use the text given when created', (done) => {
        const text = 'Example text';
        const block = notebook.createBlock(type1, text);
        expect(block.text).to.include(text);
        done();
      });

      testTypes.concat(['hint']).forEach((type2) => {
        describe(`when inserting '${type2}' blocks`, () => {
          const notebook = new Notebook;
          const baseText = 'Example text';
          let text;

          const checkBlock = function(block, type, text) {
            expect(block.type).to.equal(type);
            expect(block.text).to.include(text);
          };

          beforeEach(() => {
            notebook.blocks = [
              notebook.createBlock(type1, baseText),
            ];
            text = notebook.blocks[0].text;
          });

          it('should give blocks of the correct type',
              (done) => {
                const blocks = notebook.splitBlock(0, 1, 1, type2);

                expect(blocks).to.be.an('array').that.has.lengthOf(3);
                expect(blocks[0].type).to.equal(type1);
                expect(blocks[1].type).to.equal(type2);
                expect(blocks[2].type).to.equal(type1);
                done();
              });

          it('should split into two blocks when cursor at start', (done)=> {
            const blocks = notebook.splitBlock(0,
                0, 0, type2);

            expect(blocks).to.be.an('array').that.has.lengthOf(2);
            checkBlock(blocks[0], type2, '');
            checkBlock(blocks[1], type1, text);
            done();
          });

          it('should split into two blocks when selection at start', (done)=> {
            const to = text.length / 2;
            const blocks = notebook.splitBlock(0,
                0, to, type2);

            expect(blocks).to.be.an('array').that.has.lengthOf(2);

            checkBlock(blocks[0], type2, text.substring(0, to));
            expect(blocks[0].text).to.not.include(text.substring(to));

            checkBlock(blocks[1], type1, text.substring(to));
            expect(blocks[1].text).to.not.include(text.substring(0, to));

            done();
          });

          it('should split into two blocks when cursor at end', (done)=> {
            const blocks = notebook.splitBlock(0,
                text.length, text.length, type2);

            expect(blocks).to.be.an('array').that.has.lengthOf(2);
            checkBlock(blocks[0], type1, text);
            checkBlock(blocks[1], type2, '');

            done();
          });

          it('should split into two blocks when selection at end', (done)=> {
            const from = text.length / 2;
            const blocks = notebook.splitBlock(0,
                from, text.length, type2);

            expect(blocks).to.be.an('array').that.has.lengthOf(2);

            checkBlock(blocks[0], type1, text.substring(0, from));
            expect(blocks[0].text).to.not.include(text.substring(from));

            checkBlock(blocks[1], type2, text.substring(from));
            expect(blocks[1].text).to.not.include(text.substring(0, from));

            done();
          });

          it('should split into three blocks in middle', (done)=> {
            const from = text.length / 3;
            const to = from * 2;
            const blocks = notebook.splitBlock(0,
                from, to, type2);

            expect(blocks).to.be.an('array').that.has.lengthOf(3);

            checkBlock(blocks[0], type1, text.substring(0, from));
            expect(blocks[0].text).to.not.include(text.substring(from, to));
            expect(blocks[0].text).to.not.include(text.substring(to));

            checkBlock(blocks[1], type2, text.substring(from, to));
            expect(blocks[1].text).to.not.include(text.substring(0, from));
            expect(blocks[1].text).to.not.include(text.substring(to));

            checkBlock(blocks[2], type1, text.substring(to));
            expect(blocks[2].text).to.not.include(text.substring(0, from));
            expect(blocks[2].text).to.not.include(text.substring(from, to));

            done();
          });

          it('should replace the block when selection is the entire block',
              (done) => {
                const from = 0;
                const to = text.length;
                const blocks = notebook.splitBlock(0,
                    from, to, type2);

                expect(blocks).to.be.an('array').that.has.lengthOf(1);

                checkBlock(blocks[0], type2, text);
                done();
              });
        });
      });
    });
  });
});
