<template>
  <vue-context ref="menu">
    <block-context-menu-button
        v-for="(item, index) in contextMenuItems"
        :key="'contextMenu' + index"
        :buttonInfo="item"
        :shortKeys="shortKeys">
    </block-context-menu-button>
  </vue-context>
</template>

<script>
import {VueContext} from 'vue-context';

import BlockContextMenuButton from './BlockContextMenuButton';

export default {
  name: 'BlockContextMenu',
  components: {
    VueContext,
    BlockContextMenuButton,
  },
  props: {
    shortKeys: Object,
    blocks: Array,
    eventBus: {$on: Function, $emit: Function},
  },
  data: function() {
    return {
      contextMenuItems: [
        {
          text: 'Cut',
          shortkeyTag: 'cut',
          action: this.cut,
          // TODO: also check for selected text
          active: this.anySelected,
        },
        {
          text: 'Copy',
          shortkeyTag: 'copy',
          action: this.copy,
          active: this.anySelected,
        },
        {
          text: 'Paste',
          shortkeyTag: 'paste',
          action: this.paste,
          active: this.canPaste,
          disableShortkey: true,
        },
        null,
        {
          text: 'Delete',
          shortkeyTag: 'delete',
          action: this.delete,
          active: this.anySelected,
        },
        {
          text: 'Fold',
          shortkeyTag: 'fold',
          action: this.fold,
          active: this.anySelected,
        },
        null,
        {
          text: 'Select All',
          shortkeyTag: 'selectAll',
          action: this.selectAll,
          active: this.canSelectAll,
        },
        {
          text: 'Deselect',
          shortkeyTag: 'deselect',
          action: this.deselect,
          active: this.anySelected,
        },
      ],
      copiedBlocks: [],
      foldedBlocks: [],
      lastSelectedBlock: null,
      canPasteBlocks: false,
    };
  },
  mounted: function() {
    this.eventBus.$on('unfold', this.unfold);
    this.eventBus.$on('select-single', this.toggleSingleBlockSelection);
    this.eventBus.$on('select-range', this.selectRangeBlocks);
  },
  computed: {
    selectedCount: function() {
      let count = 0;
      for (const block of this.blocks) {
        if (block.state.isSelected) {
          ++ count;
        }
      }
      return count;
    },
  },
  methods: {
    /**
     * @return {Boolean} whether there is a selected block
     */
    anySelected: function() {
      return this.selectedCount > 0;
    },

    /**
     * @return {Boolean} Whether select all should be active
     */
    canSelectAll: function() {
      return this.selectedCount < this.blocks.length
          && document.activeElement.nodeName !== 'TEXTAREA'
          && document.activeElement.nodeName !== 'INPUT';
    },

    /**
     * @return {Boolean} Whether paste should be active
     */
    canPaste: function() {
      return this.canPasteBlocks;
    },

    /**
     * @event editpage#click opens block context menu
     * @param {Object} event The event associated with the click
     * @param {Object} block If not null, select this block
     */
    open: function(event, block = null) {
      if (block && !this.selectedCount) {
        block.state.isSelected = true;
      }
      this.canPasteBlocks = this.getBlocksFromClipboard() !== null;
      this.$refs.menu.open(event);
    },

    /**
     * Retrieve copied blocks from the clipboard
     * @return {Array|null} The blocks on the clipboard,
     *    or null if there are no blocks on the clipboard
     */
    getBlocksFromClipboard: function() {
      const {clipboard} = require('electron');
      const clipboardContent = clipboard.readText();

      let clipboardBlocks;
      try {
        clipboardBlocks = JSON.parse(clipboardContent);
      } catch (e) {
        // Not valid JSON
        return null;
      }

      // Make sure it is a non-empty array
      if (!Array.isArray(clipboardBlocks) || !clipboardBlocks.length) {
        return null;
      }

      // Make sure all elements are blocks
      for (const block of clipboardBlocks) {
        if (!block.hasOwnProperty('type') ||
            !block.hasOwnProperty('text') &&
            !block.hasOwnProperty('id')) {
          return null;
        }
      }
      return clipboardBlocks;
    },

    /**
     * Find the index of the given block in the blocks array
     * @param {Block} block The block to search for
     * @return {Number} The index of the block, or -1 if it cannot be found
     */
    findBlockIndex: function(block) {
      return this.blocks.indexOf(block);
    },

    /**
     * Toggle selection of a single block
     *
     * @param {Object} block The block to toggle selection of
     */
    toggleSingleBlockSelection: function(block) {
      if (block.state.foldStatus.startFold) {
        this.lastSelectedBlock = block;
        this.selectRangeBlocks(block.state.foldStatus.endBlock,
            !block.state.isSelected);
        return;
      }

      block.state.isSelected = !block.state.isSelected;
      if (block.state.isSelected) {
        this.lastSelectedBlock = block;
      }
    },

    forceSelectSingleBlock: function(block) {
      if (!block.state.isSelected) {
        this.toggleSingleBlockSelection(block);
      }
    },

    /**
     * Select a range of blocks
     *
     * @param {Object} block The last selected block
     * @param {Boolean} enable Whether to enable or disable selection
     */
    selectRangeBlocks: function(block, enable = true) {
      this.deselect();

      let lastSelectedBlock = this.lastSelectedBlock;
      if (this.findBlockIndex(lastSelectedBlock) === -1) {
        lastSelectedBlock = this.blocks[0];
      }

      this.selectBlocksBetween(lastSelectedBlock, block, enable);
    },

    /**
     * Select all blocks between two given blocks
     * (including these two blocks)
     *
     * @param {Block} fromBlock First given block
     * @param {Block} toBlock Second given block
     * @param {Boolean} enable Whether to enable or disable selection
     */
    selectBlocksBetween: function(fromBlock, toBlock, enable = true) {
      const fromIndex = this.findBlockIndex(fromBlock);
      const toIndex = this.findBlockIndex(toBlock);

      const minIndex = Math.min(fromIndex, toIndex);
      const maxIndex = Math.max(fromIndex, toIndex);

      for (let i = minIndex; i <= maxIndex; ++ i) {
        const block = this.blocks[i];
        if (enable !== block.state.isSelected) {
          if (block.state.foldStatus.startFold) {
            this.forceSelectSingleBlock(block);
          } else {
            this.toggleSingleBlockSelection(block);
          }
        }
      }
      this.lastSelectedBlock = toBlock;
    },

    /**
     * Select all blocks between the currently first and last selected block
     * (including those two blocks themselves).
     */
    selectionFill: function() {
      let startBlock = -1;
      let endBlock = -1;
      for (let i = 0; i < this.blocks.length; ++ i) {
        const block = this.blocks[i];
        if (block.state.isSelected) {
          if (startBlock === -1) {
            startBlock = block;
          }
          endBlock = block;
        }
      }

      this.selectBlocksBetween(startBlock, endBlock);
    },

    /**
     * Toggle selection between all blocks and no blocks
     * @param {Boolean} selectStatus whether to
     *  select or deselect all blocks
     */
    selectAll: function(selectStatus = true) {
      for (const block of this.blocks) {
        block.state.isSelected = selectStatus;
      }
    },

    /**
     * Deselect all selected blocks
     */
    deselect: function() {
      this.selectAll(false);
    },

    /**
     * Deletes the selected blocks
     */
    delete: function() {
      this.selectInputBlocks();

      const blockIndices = [];
      for (let i = 0; i < this.blocks.length; ++i) {
        const block = this.blocks[i];
        if (block.state.isSelected) {
          block.state.isSelected = false;
          blockIndices.push(i);
        }
      }
      this.eventBus.$emit('removeBlocks', blockIndices);
    },


    /**
     * Selects both input blocks of the input areas that already have at
     * least one selected input block
     */
    selectInputBlocks: function() {
      const selectedInputIds = [];

      // Keep track of all input ids of which at least
      // one of the input blocks has been selected.
      for (let i = 0; i < this.blocks.length; i++) {
        const block = this.blocks[i];
        if (block.type === 'input' && block.state.isSelected) {
          selectedInputIds.push(block.id);
        }
      }

      // Select all blocks of which at least one
      // block with the same id has been selected
      for (let i = 0; i < this.blocks.length; i++) {
        const block = this.blocks[i];
        if (block.type === 'input' && selectedInputIds.includes(block.id)) {
          this.forceSelectSingleBlock(block);
        }
      }
    },

    /**
     * Copies selected blocks to the clipboard as JSONs
     */
    copy: function() {
      this.selectInputBlocks();

      const blocksToCopy = [];

      for (const block of this.blocks) {
        if (block.state.isSelected) {
          blocksToCopy.push(block);
        }
      }

      const {clipboard} = require('electron');
      const jsonBlocks = JSON.stringify(blocksToCopy);
      clipboard.writeText(jsonBlocks);
    },

    /**
     * Cuts selected blocks to the clipboard as JSONs
     */
    cut: function() {
      this.copy();
      this.delete();
    },

    /**
     * Pastes blocks from clipboard
     * @param {ClipboardEvent|MouseEvent} event
     *    The event associated with the paste
     */
    paste: function(event) {
      const clipboardBlocks = this.getBlocksFromClipboard();
      if (clipboardBlocks !== null) {
        this.eventBus.$emit('insertBlocks', clipboardBlocks);
        // Prevent normal pasting from taking place
        event.preventDefault();
        event.stopPropagation();
      }
    },

    /**
     * Folds the selected blocks
     */
    fold: function() {
      // Select everything that needs to be part of the fold
      this.selectionFill();
      this.selectInputBlocks();

      let startBlock = -1;
      let startBlockIndex = -1;
      let endBlock = -1;
      let endBlockIndex = -1;

      // Find first and last block of selection
      for (let i = 0; i < this.blocks.length; ++ i) {
        const block = this.blocks[i];
        if (block.state.isSelected) {
          if (startBlock === -1) {
            startBlock = block;
            startBlockIndex = i;
          }
          endBlock = block;
          endBlockIndex = i;
        }
      }

      for (let i = startBlockIndex; i <= endBlockIndex; ++ i) {
        this.forceSelectSingleBlock(this.blocks[i]);
        this.blocks[i].state.foldStatus.startFold = false;
        this.blocks[i].state.foldStatus.isFolded = true;
        this.blocks[i].state.foldStatus.endBlock = null;
      }

      startBlock.state.foldStatus.startFold = true;
      startBlock.state.foldStatus.endBlock = endBlock;
    },
    unfold: function(block) {
      const startBlockIndex = this.findBlockIndex(block);
      const endBlockIndex =
          this.findBlockIndex(block.state.foldStatus.endBlock);

      for (let i = startBlockIndex; i <= endBlockIndex; ++ i) {
        this.blocks[i].state.foldStatus.isFolded = false;
      }
      block.state.foldStatus.endBlock = null;
      block.state.foldStatus.startFold = false;
    },
  },
};
</script>

<style lang="scss" scoped>
@import '../../../assets/sass/_colors.scss';
  .v-context {
    @include theme(background-color, color-gray-light);
  }
</style>
