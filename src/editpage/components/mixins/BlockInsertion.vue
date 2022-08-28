<script>
/**
 * ProofWindow's block insertion functionality
 */
import {writeActivity} from '@/activity-log';

export default {
  name: 'BlockInsertion',
  data: function() {
    return {
      // this will be replaced by proofwindow/coqinteraction
      eventBus: null,
    };
  },
  mounted: function() {
    this.eventBus.$on('insertBlocks', this.insertBlocks);
    this.eventBus.$on('removeBlocks', this.removeBlocks);
    this.eventBus.$on('insertCode', this.insertCode);
    this.eventBus.$on('insertText', this.insertText);
    this.eventBus.$on('insertHint', this.insertHint);
    this.eventBus.$on('insertInputArea', this.insertInputArea);
  },
  methods: {
    /**
     * Determine the index to insert blocks at
     *
     * @return {Number} the index to insert blocks at
     *    or -1 if none is available
     */
    insertionIndex: function() {
      // If we have an interblock cursor, insert there
      if (this.$refs.editWindow.selectedInterblock !== -1) {
        return this.$refs.editWindow.selectedInterblock;
      }

      // If we are editing a block, insert after it
      if (this.cursorPos.block !== -1 &&
          this.cursorPos.block < this.notebook.blocks.length) {
        return this.cursorPos.block + 1;
      }

      // If we are in an exercise sheet
      if (this.notebook.exerciseSheet) {
        // Return the end of the last input area
        for (let i = this.notebook.blocks.length - 1; i >= 0; i--) {
          if (this.notebook.blocks[i].type === 'input'
              && !this.notebook.blocks[i].start) {
            return i;
          }
        }
        // Or -1 if there are no input areas
        return -1;
      }

      // Otherwise, insert after the last block
      return this.notebook.blocks.length;
    },

    /**
     * Determine whether the given block is in an input field, It also updates
     * the inInputField of all blocks up to this index.
     *
     * @param {Number} index The index of the block
     * @return {Boolean} Whether it is an input field
     */
    isInInputField: function(index) {
      let inInputField = false;
      for (let i = 0; i < index; i++) {
        const block = this.notebook.blocks[i];
        block.state.inInputField = inInputField;
        if (block.type === 'input') {
          inInputField = block.start;
          block.state.inInputField = false;
        }
      }
      return inInputField;
    },

    /**
     * Insert blocks at the cursor position
     *
     * @param {Block} blocks The blocks to insert
     */
    insertBlocks: function(blocks) {
      this.undoRedo.startGroup();
      for (let i = 0; i < blocks.length; i++) {
        const block = blocks[i];
        if (block.type !== 'input') {
          this.insertBlock(block.type, block.text, true);
        } else {
          this.insertInputBlock(block.start);
        }
      }
      this.undoRedo.endGroup();
    },

    /**
     * Insert a block at the cursor position
     *
     * @param {String} type The type the block should have
     * @param {String} content The content the block should have
     * @param {Boolean} focusAfter whether to focus on the block after
     */
    insertBlock: function(type, content = '', focusAfter = false) {
      const inBlock = this.cursorPos.block !== -1 &&
          this.cursorPos.block < this.notebook.blocks.length;

      let index;
      if (inBlock && focusAfter) {
        // We are pasting while editing a block
        index = this.$refs.editWindow.focusedElement + 1;
        this.$refs.editWindow.blurSource();
        this.$refs.editWindow.selectedInterblock = index;
      } else {
        index = this.insertionIndex();
      }

      writeActivity('inserting-block', {
        file: this.notebook.filePath,
        blockType: type,
        blockIndex: index,
        insertingBlockInBlock: inBlock,
        tabIndex: this.index,
      });

      if (inBlock && !focusAfter) {
        // We are in a block
        const newBlocks = this.notebook.splitBlock(this.cursorPos.block,
            this.cursorPos.fromIndex, this.cursorPos.toIndex, type);

        let newIndex;
        if (newBlocks.length === 3 || this.cursorPos.fromIndex !== 0) {
          newIndex = 1;
        } else {
          newIndex = 0;
        }

        if (content !== '') {
          newBlocks[newIndex] = content;
        }
        this.undoRedo.splitBlock(this.cursorPos.block, newBlocks);
        this.$refs.editWindow.setFocusedElement(
            this.cursorPos.block + newIndex);
      } else {
        if (index < 0) {
          // There was no valid place to insert at
          return;
        }

        const block = this.notebook.createBlock(type, content,
            this.isInInputField(index));
        if (block) {
          this.undoRedo.addBlocks(index, block);
          if (!focusAfter) {
            this.$refs.editWindow.setFocusedElement(index);
          } else if (this.$refs.editWindow.selectedInterblock > -1) {
            this.$refs.editWindow.selectedInterblock++;
          }
        }
      }
    },

    /**
     * Remove the block at the given index
     *
     * @param {Array} index The indices of the blocks to remove
     */
    removeBlocks: function(index) {
      this.undoRedo.startGroup();
      const blockTypes = {};
      for (let i = index.length - 1; i >= 0; i--) {
        blockTypes[i] = this.notebook.blocks[i].type;
        this.undoRedo.removeBlocks(index[i], 1);
      }
      writeActivity('removing-blocks', {
        file: this.notebook.filePath,
        blocksRemoved: blockTypes,
        tabIndex: this.index,
      });
      this.undoRedo.endGroup();
    },

    /**
     * Insert an empty text block at the cursor position
     */
    insertText: function() {
      this.insertBlock('text');
    },

    /**
     * Insert an empty code block at the cursor position
     */
    insertCode: function() {
      this.insertBlock('code');
    },

    /**
     * Insert an empty hint block at the cursor position
     */
    insertHint: function() {
      if (this.notebook.exerciseSheet) {
        console.log('can\'t add hint to exercise');
        return;
      }
      this.insertBlock('hint');
    },

    /**
     * Insert the two blocks of an input area
     */
    insertInputArea: function() {
      this.undoRedo.startGroup();
      this.insertInputBlock(true);
      this.insertInputBlock(false);
      this.undoRedo.endGroup();
    },

    /**
     * Insert an input block
     *
     * @param {Boolean} start Whether the block to insert is a start block.
     */
    insertInputBlock: function(start) {
      // Can not add input blocks in exercise sheet
      if (this.notebook.exerciseSheet) {
        console.log('can\'t add input to exercise');
        return;
      }

      // Can not add input blocks beyond notebook boundaries
      const index = this.insertionIndex();
      if (index < 0) {
        return;
      }

      // Find existing input blocks
      const existingOpeningIds = [];
      const existingClosingIds = [];

      for (let i = 0; i < this.notebook.blocks.length; i++) {
        const block = this.notebook.blocks[i];
        if (block.type === 'input') {
          if (block.start) {
            existingOpeningIds.push(block.id);
          } else {
            existingClosingIds.push(block.id);
          }
        }
      }

      // Generate new input block (either starting or closing)
      let newId = '';
      let inInputField;
      if (start) {
        newId = this.generateUniqueInputId(existingOpeningIds);
        inInputField = this.isInInputField(index);
      } else {
        newId = this.generateUniqueInputId(existingClosingIds);
        inInputField = (!existingOpeningIds.includes(newId));
      }

      // Can not add input field in input field
      if (inInputField) {
        console.log('don\'t add input field in input field');
        return;
      }

      // If we are inside a block
      const cursorBlockIndex = this.cursorPos.block;
      if (this.cursorPos.block >= 0) {
        // If this block is empty
        if (this.notebook.blocks[cursorBlockIndex].text === '') {
          this.$refs.editWindow.blurSource();
          this.$refs.editWindow.selectedInterblock = cursorBlockIndex;
          this.insertInputBlock(start);
          return;
        }

        const cursorAtStart = this.cursorPos.fromIndex === 0;
        let newIndex = this.cursorPos.block;
        if (!cursorAtStart) {
          newIndex++;
        }

        // Split up the block by "adding" a block of the non-existing type
        // 'none'. This ensures that the blocks are split at the correct
        // location, but no extra blocks are added. NOTE: if there is content
        // selected, we split at the start of the selection.
        // TODO: place selection as a new block inside input area
        const newBlocks = this.notebook.splitBlock(this.cursorPos.block,
            this.cursorPos.fromIndex, this.cursorPos.fromIndex, 'none');
        this.undoRedo.splitBlock(this.cursorPos.block, newBlocks);

        this.$refs.editWindow.blurSource();
        this.$refs.editWindow.selectedInterblock = newIndex;
        this.insertInputBlock(start);
        return;
      }

      const blocks = this.notebook.createInputBlock(newId, start);
      this.undoRedo.addBlocks(index, blocks);

      if (this.$refs.editWindow.selectedInterblock !== -1) {
        this.$refs.editWindow.selectedInterblock++;
      }
    },

    /**
     * Generate a unique id for input fields, given the list of existing ids
     * @param {Array} existingIds An array of all ids already in use
     * @return {string} A string that is not in the array existingIds
     */
    generateUniqueInputId: function(existingIds) {
      const prefix = 'input-';
      let count = 1;
      while (existingIds.includes(prefix + count)) {
        count++;
      }

      return prefix + count;
    },
  },
};
</script>
