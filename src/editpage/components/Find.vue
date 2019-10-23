<template>
  <div class="find-wrapper">
        <span class="find">
          <input type="text" v-model="find" placeholder="Find ..."
                 ref="findInput"/>
          <button class="find-button" :disabled="!find"
                  @click='findNextWord(1, false)'>
            Next
          </button>
          <button class="find-button" :disabled="!find"
                  @click='findNextWord(-1, false)'>
            Prev
          </button>
        </span>
    <span class="replace">
          <input type="text" v-model="replace" placeholder="Replace with ..."/>
          <button class="find-button" :disabled="!find"
                  @click='findNextWord(1, true)'>
            Replace
          </button>
          <button class="find-button" :disabled="!find"
                  @click='replaceAll()'>
            Replace all
          </button>
        </span>
  </div>
</template>

<script>
export default {
  props: {
    blocks: Array,
    exercise: Boolean,
    eventBus: {},
  },

  data: function() {
    return {
      name: 'Find',
      find: '',
      // The index of the block the currently highlighted result in blocks
      findPos: -1,
      // The index of the block the currently highlighted result in findList
      findIndex: -1,
      findCursor: null,
      findFrom: -1,
      findTo: -1,
      marker: null,
      currentCm: null,
      replace: '',
      focusedElement: -1,
      onCodeMirrorReady: () => {},
    };
  },

  methods: {
    changeFocusedElement: function(index, find = false) {
      if (!find) {
        this.findPos = -1;
      }
      this.findCursor = null;
      this.focusedElement = index;
    },

    /**
     * Shows a message in a dialog to the user
     *
     * @param {string} message  The message to show to the user
     */
    showMessage: function(message) {
      const {dialog} = require('electron').remote;

      const dialogOptions = {
        type: 'info', title: 'Waterproof',
        buttons: ['OK'], message: message,
      };

      dialog.showMessageBox(dialogOptions);
    },

    findNextWord: function(direction, doReplace) {
      // No matches to the query were found
      if (this.findList.length === 0) {
        this.showMessage('No matches to your query were found');
        return false;
      }

      // If Replace is chosen, replace found string if it is not read-only
      if (doReplace && !this.replaceCurrent()) {
        return false;
      }

      // If no string was found yet, find string
      if (this.findPos < 0) {
        this.findNextBlock(direction);
        this.findCursor = null;
      }

      if (this.marker) {
        this.marker.clear();
      }

      if (this.findCursor === null) {
        if (this.currentCm) {
          this.setFindCursor(direction);
          this.markWord(direction);
        } else {
          this.onCodeMirrorReady = () => {
            this.currentCm.setOption('readOnly',
                this.findList[this.findIndex].readOnly);
            this.setFindCursor(direction);
            this.markWord(direction);
          };
        }
      } else if ((direction === 1 && !this.findCursor.findNext())
              || (direction === -1 && !this.findCursor.findPrevious())) {
        if (this.findList.length === 1 &&
            this.blocks[this.findPos].text.toLowerCase()
                .includes(this.find.toLowerCase())
        ) {
          this.setFindCursor(direction);
          this.markWord(direction, doReplace);
        } else {
          this.findNextBlock(direction);

          this.onCodeMirrorReady = () => {
            this.currentCm.setOption('readOnly',
                this.findList[this.findIndex].readOnly);
            this.setFindCursor(direction);
            this.markWord(direction, doReplace);
          };
        }
      } else {
        this.findFrom = this.findCursor.from();
        this.findTo = this.findCursor.to();
        this.marker = this.currentCm.markText(this.findFrom, this.findTo,
            {className: 'highlightText', clearOnEnter: true});
        const wordCoords = this.currentCm.charCoords(this.findFrom, 'local');
        this.$parent.scrollToWord(wordCoords);
      }
    },

    replaceCurrent: function() {
      if (!this.findCursor) return true; // There is no current result

      if (!this.findList[this.findIndex].readOnly) {
        this.findCursor.replace(this.replace);
        if (this.findList.length === 0) {
          this.marker = this.currentCm.markText(this.findCursor.from(),
              this.findCursor.to(),
              {className: 'highlightText', clearOnEnter: true});
          return false;
        }
      } else {
        this.showMessage('You may not replace this');
        return false;
      }
      return true;
    },

    setFindCursor: function(next) {
      if (next === 1) {
        this.findCursor = this.currentCm.getSearchCursor(this.find,
            {line: 0, ch: 0}, true);
      } else if (next === -1) {
        this.findCursor = this.currentCm.getSearchCursor(this.find,
            {
              line: this.currentCm.lastLine(),
              ch: (this.currentCm.getLine(
                  this.currentCm.lastLine() ).length),
            },
            true);
      }
    },

    markWord: function(direction) {
      if (direction === 1) {
        this.findCursor.findNext();
      } else if (direction === -1) {
        this.findCursor.findPrevious();
      }

      this.findFrom = this.findCursor.from();
      this.findTo = this.findCursor.to();

      this.marker = this.currentCm.markText(this.findFrom, this.findTo,
          {className: 'highlightText', clearOnEnter: true});
      const wordCoords = this.currentCm.charCoords(this.findFrom, 'local');
      this.$parent.scrollToWord(wordCoords);
    },

    findNextBlock: function(direction) {
      if (this.findPos >= 0 && this.findList[this.findIndex]
              && this.findPos === this.findList[this.findIndex].index) {
        // There is a currently active search result
        const l = this.findList.length;
        this.findIndex = (((this.findIndex + direction) % l) + l) % l;
        this.findPos = this.findList[this.findIndex].index;
      } else if (this.focusedElement < 0) {
        // There is not currently active block
        this.findPos = this.findList[0].index;
        this.findIndex = 0;
      } else {
        // There is a currently active block, but no current search result
        for (let i = 0; i < this.findList.length; i++) {
          if (this.findList[i].index >= this.focusedElement ||
              this.focusedElement >
                  this.findList[this.findList.length - 1].index) {
            this.findIndex = i;
            break;
          }
        }
        if (direction === -1) {
          const l = this.findList.length;
          this.findIndex = (((this.findIndex - 1) % l) + l) % l;
        }
        this.findPos = this.findList[this.findIndex].index;
      }
      this.eventBus.$emit('set-focus', this.findPos, true);
      // this.setFocusedElement(this.findPos, true);
    },

    replaceAll: function() {
      const blocks = this.blocks;
      const changes = [];

      // We iterate over the block in reversed order to make sure that the
      // removal of a block does not change the index of blocks changed after it
      for (let i = blocks.length-1; i >= 0; i--) {
        if (blocks[i].type !== 'input' &&
            (blocks[i].state.inInputField || !this.exercise)) {
          const newText = blocks[i].text.replace(
              new RegExp(this.find, 'gi'), (match) => {
                return this.replace;
              }
          );
          if (newText !== '' || i === this.focusedElement) {
            changes.push({
              type: 'input',
              blockIndex: i,
              newValue: newText,
            });
          } else {
            changes.push({
              type: 'remove-block',
              blockIndex: i,
              newValue: newText,
            });
          }
        }
      }

      if (changes.length === 0) {
        return;
      }
      this.eventBus.$emit('changeMultipleInputs', changes);
    },

    resetFind: function() {
      if (this.marker) {
        this.marker.clear();
      }
      this.findPos = -1;
      this.findIndex = -1;
      this.findCursor = null;
      this.findFrom = -1;
      this.findTo = -1;
    },
  },

  computed: {
    findList() {
      const blocks = this.blocks;
      const exercise = this.exercise;
      const list = [];
      for (let i = 0; i < blocks.length; i++) {
        if (blocks[i].type !== 'input' &&
            blocks[i].text.toLowerCase().includes(this.find.toLowerCase())) {
          if (exercise &&
                !blocks[i].state.inInputField) {
            list.push({block: blocks[i], index: i, readOnly: true});
          } else {
            list.push({block: blocks[i], index: i, readOnly: false});
          }
        }
      }
      return list;
    },
  },

  watch: {
    'find': function(newVal, oldVal) {
      this.resetFind();
    },
  },
};
</script>

<style lang="scss">
@import "../../assets/sass/pages/edit.scss";

.find {
  margin-left: 10px;
  display: flex;
  flex-flow: row nowrap;
  .topbar-button {
    font-size: 12px;
  }
}

.find-wrapper {
  display: flex;
  flex-flow: row wrap;
  z-index: 5;
  background-color: $color-primary;
  position: fixed;
  bottom: 5px;
  max-width: inherit;
  padding: 5px 5px 5px 5px;
  font-size: 12px;
}

#find-button {
  @extend .topbar-button;
  font-size: 12pt;
}

.replace {
  margin-left: 10px;

  .topbar-button {
    font-size: 12px;
  }
}
</style>
