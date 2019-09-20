import {
  UndoRedo,
  MAX_BUFFER_SIZE,
} from '../../../src/editpage/components/undoredo';

const chai = require('chai');
const expect = chai.expect;

let undoRedo;
let notebook;

const block1 = {
  type: 'code',
  text: 'some text',
  state: {},
};

const block2 = {
  type: 'code',
  text: 'some new text',
  state: {},
};

/**
 * We must clone blocks we use before adding them, because undoRedo will change
 * their contents which is what we want in the real program, but not here since
 * then we couldn't reliably re-use those blocks.
 * @param {Object} block the notebook block to clone
 * @return {Object} a deep clone of the block
 */
function clone(block) {
  return JSON.parse(JSON.stringify(block));
}

describe('undo redo', () => {
  beforeEach(() => {
    notebook = {blocks: []};
    undoRedo = new UndoRedo(notebook);
  });

  it('should correctly execute an add-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(clone(block1)));
    expect(notebook.blocks).to.deep.equal([block1]);
    done();
  });

  it('should correctly execute an input command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    undoRedo.changeInput(0, block2.text);
    expect(notebook.blocks).to.deep.equal([block2]);
    done();
  });

  it('should correctly execute a remove-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.removeBlocks(0, 1);
    expect(notebook.blocks).to.deep.equal([]);
    done();
  });

  it('should correctly execute a split-block command', (done) => {
    const initialBlock = {
      type: 'code',
      text: 'this is some initial text',
      state: {},
    };
    undoRedo.addBlocks(initialBlock);
    undoRedo.splitBlock(0, [clone(block1), clone(block2)]);
    expect(notebook.blocks).to.deep.equal([block1, block2]);
    done();
  });


  it('should correctly undo an add-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([]);
    done();
  });

  it('should correctly undo an input command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    undoRedo.changeInput(0, block2.text);
    expect(notebook.blocks).to.deep.equal([block2]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    done();
  });

  it('should correctly undo a remove-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.removeBlocks(0, 1);
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    done();
  });


  it('should correctly redo an add-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([block1]);
    done();
  });

  it('should correctly redo an input command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    undoRedo.changeInput(0, block2.text);
    expect(notebook.blocks).to.deep.equal([block2]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([block2]);
    done();
  });

  it('should correctly redo a remove-blocks command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.removeBlocks(0, 1);
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([]);
    done();
  });


  it('should combine an add-block and add-input command', (done) => {
    const block = {
      type: 'code',
      text: '',
      state: {},
    };
    undoRedo.addBlocks(0, clone(block));
    undoRedo.changeInput(0, block2.text);
    // The two commands should be one
    expect(notebook.blocks).to.deep.eq([block2]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.eq([]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.eq([block2]);
    done();
  });

  it('should combine a clear-block and remove-input command', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.blocks).to.deep.equal([block1]);

    // Set the content of the block empty, then remove it
    undoRedo.changeInput(0, '');
    undoRedo.removeBlocks(0, 1);
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([]);
    done();
  });

  it('should handle compound commands correctly', (done) => {
    // In a single command, add a block and then change its text
    undoRedo.startGroup();
    undoRedo.addBlocks(0, clone(block1));
    undoRedo.changeInput(0, block2.text);
    undoRedo.endGroup();

    // We should now revert to an empty notebook in only a single undo
    expect(notebook.blocks).to.deep.equal([block2]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([block2]);

    done();
  });

  it('should combine a compound command and a change-input block', (done) => {
    const emptyBlock = {
      type: 'code',
      text: '',
      state: {},
    };

    // First, create a notebook in a way that ends in adding an empty block
    undoRedo.startGroup();
    undoRedo.addBlocks(0, [clone(block1), clone(block2)]);
    undoRedo.removeBlocks(1, 1);
    undoRedo.addBlocks(1, emptyBlock);
    undoRedo.endGroup();

    // Then, set text to the new block
    undoRedo.changeInput(1, block2.text);

    // Now, everything done until here should be a single action
    expect(notebook.blocks).to.deep.equal([block1, block2]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([block1, block2]);

    done();
  });

  it('should ignore duplicate identical input-change commands', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    undoRedo.changeInput(0, 'this is new text');
    undoRedo.changeInput(0, 'this is new text');

    const result = {
      type: 'code',
      text: 'this is new text',
      state: {},
    };

    expect(notebook.blocks).to.deep.equal([result]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.undo();
    expect(notebook.blocks).to.deep.equal([]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([block1]);
    undoRedo.redo();
    expect(notebook.blocks).to.deep.equal([result]);
    done();
  });

  it('should update the unsavedChanges variable after any edit', (done) => {
    notebook.unsavedChanges = false;
    undoRedo.addBlocks(0, clone(block1));
    expect(notebook.unsavedChanges).to.equal(true);
    notebook.unsavedChanges = false;
    undoRedo.undo();
    expect(notebook.unsavedChanges).to.equal(true);
    notebook.unsavedChanges = false;
    undoRedo.redo();
    expect(notebook.unsavedChanges).to.equal(true);
    notebook.unsavedChanges = false;
    done();
  });

  it('should not update unsavedChanges when an no-op is done', (done) => {
    notebook.unsavedChanges = false;

    // Nothing to undo, so this does not change the notebook
    undoRedo.undo();
    expect(notebook.unsavedChanges).to.equal(false);

    undoRedo.addBlocks(0, clone(block1));
    notebook.unsavedChanges = false;

    // Nothing to redo, so this does not change the notebook
    undoRedo.redo();
    expect(notebook.unsavedChanges).to.equal(false);
    done();
  });

  it('should should allow a maximum of MAX_BUFFER_SIZE changes', (done) => {
    undoRedo.addBlocks(0, clone(block1));
    for (let i = 1; i < MAX_BUFFER_SIZE; i++) {
      const newText = (i % 2 == 0) ? 'a' : 'b';
      undoRedo.changeInput(0, newText);
    }
    // The undo stack is now at max capacity
    expect(undoRedo.undoStack.length).to.be.equal(MAX_BUFFER_SIZE);

    // So the next change will not increase the size
    undoRedo.changeInput(0, 'c');
    expect(undoRedo.undoStack.length).to.be.equal(MAX_BUFFER_SIZE);

    // After undoing everything, the redo stack should be of maximum size
    for (let i = 0; i < MAX_BUFFER_SIZE; i++) {
      undoRedo.undo();
    }
    expect(undoRedo.undoStack.length).to.be.equal(0);
    expect(undoRedo.redoStack.length).to.be.equal(MAX_BUFFER_SIZE);
    done();
  });
});
