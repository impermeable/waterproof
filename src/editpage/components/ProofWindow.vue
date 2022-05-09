<template>
  <b-tab>
  <template slot="title">
    <div class="tab-text" @click.middle.prevent="close"
         :title="notebook.filePath || 'untitled'">
      <template v-if="notebook.unsavedChanges">
        *
      </template>
      {{notebook.getName().trim()}}
    </div>
    <img @click.middle.prevent="close" @click.stop="close" alt="x"
         class="close-cross" src="../../assets/images/cross-blue.svg"/>
  </template>
  <div class="proof-and-side-window">
    <div class="proof-window">
      <edit-window :blocks="notebook.blocks" :exercise="notebook.exerciseSheet"
                  :coq="coq" ref="editWindow" :debug="debug"
                  :executeIndex="executedIndex"
                  :pendingIndex="startedExecutionIndex"
                  :tabindex="index" :event-bus="eventBus"
                  :notebook-uri="notebook.filePath"
                  :showFind="showFind" :shortKeys="shortKeys" />
      <response-window :event-bus="eventBus"
                      :goals="goals" :addError="addError" :ready="ready">
      </response-window>
    </div>
    <side-window :event-bus="eventBus">
    </side-window>
  </div>
  </b-tab>
</template>
<script>
import BlockInsertion from './mixins/BlockInsertion';
import ResponseWindow from './response/ResponseWindow';
import EditWindow from './EditWindow';
import Notebook from '../../io/notebook';
import SideWindow from './assistance/SideWindow';
import {UndoRedo} from './undoredo';
import CoqInteraction from './mixins/CoqInteraction';
import FileInteraction from './mixins/FileInteraction';
import Vue from 'vue';
import {writeActivity} from '@/activity-log';

const snoopingOnEvents = false;

export default {
  name: 'ProofWindow',
  mixins: [BlockInsertion, CoqInteraction, FileInteraction],
  created() {
    if (snoopingOnEvents) {
      const oldEmit = this.eventBus.$emit;
      this.eventBus.$emit = function(...args) {
        console.log('got event: ' + args[0]);
        oldEmit.apply(this, args);
      };
    }

    this.loadNotebook();
  },
  components: {
    EditWindow,
    ResponseWindow,
    SideWindow,
  },
  props: {
    uri: {
      type: String,
      default: null,
    },
    debug: {
      type: Boolean,
    },
    index: Number,
    shortKeys: Object,
  },
  data: function() {
    return {
      eventBus: new Vue(),
      notebook: new Notebook(),
      undoRedo: new UndoRedo(null),
      lastSearch: null,
      showFind: false,
      focusInputs: false,
      cursorPos: {
        block: -1,
      },
    };
  },
  computed: {
    coqCode: function() {
      let code = '';
      for (const block of this.notebook.blocks) {
        if (block.type === 'code') {
          code += block.text + ' ';
        }
      }
      return code;
    },
  },
  watch: {
    coqCode: function(newCode) {
      this.coq.setContent(newCode);

      let index = 0;

      // If something in an input block changes, remove any underlining error.
      this.notebook.blocks
          .filter((block) => block.type === 'code')
          .forEach((block) => {
            block.state.error = null;
            block.state.textIndex = index;
            index += block.text.length + 1;
          });
    },
  },
  methods: {
    /**
     * Loads the notebook at the path specified by this.uri into this window,
     * and creates a new serapi worker
     */
    loadNotebook: function() {
      if (this.notebook && this.notebook.filePath === this.uri) {
        return;
      } else {
        this.ready = false;
      }

      if (this.coq) {
        this.coq.stop();
      }

      this.startCoq().then(() => {
        this.notebook = new Notebook;
        this.notebook.filePath = this.uri;

        const notebookType = this.notebook.exerciseSheet ?
            'exercise sheet' : 'notebook';
        if (this.uri !== null) {
          this.notebook.read(() => {
            writeActivity('loaded-file', {
              file: this.uri,
              tabIndex: this.index,
            });

            // When the notebook is loaded, update to enable the buttons for
            // inserting blocks etc.
            this.updateButtons();
            this.coq.validate = (sentence) => {
              for (const illegalTerm of this.notebook.commandBlacklist) {
                if (sentence.startsWith(illegalTerm)) {
                  throw new Error(`the command "${illegalTerm}" is` +
                  `not allowed in this ${notebookType}`);
                }
              }
            };
          });
        }

        this.undoRedo = new UndoRedo(this.notebook);
      });
    },

    /**
     * Finds the current index of the cursor in the string that
     * would be obtained from concatenating all code blocks.
     *
     * @return {number}  The index of the cursor in the code
     */
    findCodeIndex: function() {
      let blockCount = 0;
      let codeIndex = 0;
      for (const block of this.notebook.blocks) {
        if (blockCount === this.cursorPos.block) {
          if (block.type === 'code') {
            codeIndex += this.cursorPos.toIndex;
          }
          break;
        } else {
          if (block.type === 'code') {
            codeIndex += block.text.length + 1;
          }
          ++ blockCount;
        }
      }
      return codeIndex;
    },

    /**
     * Closes the notebook and the tab of this ProofWindow
     */
    close: function() {
      // this.coq.stop();
      this.$parent.$parent.closeTab(this.index);
    },

    setCursorPos: function(cursor) {
      this.cursorPos = cursor;
    },

    changeInput: function(type, blockIndex, newValue) {
      if (type === 'input') {
        this.undoRedo.changeInput(blockIndex, newValue);
      } else if (type === 'remove-block') {
        this.undoRedo.removeBlocks(blockIndex, 1);
      }
    },

    changeMultipleInputs: function(changes) {
      this.undoRedo.startGroup();

      changes.forEach((change) => {
        this.changeInput(change.type, change.blockIndex, change.newValue);
      });

      this.undoRedo.endGroup();
    },

    /**
     * Undoes the latest edit to the notebook
     */
    undo: function() {
      this.undoRedo.undo();
    },

    /**
     * Redoes the latest undid edit to the notebook
     */
    redo: function() {
      this.undoRedo.redo();
    },

    /**
     * To be called after the execution of some code succeeded
     * Updates the goals if there were changes, updates
     * the execution index, and removes errors
     *
     * @param {string} goal  The new goals, or null when there were no changes
     * @param {number} index  The index to where the code was executed
     */
    executeSuccess: function(goal, index) {
      if (goal !== null) {
        this.goals = goal;
      }
      this.executedIndex = index;

      // Also clear errors
      this.notebook.blocks
          .filter((block) => block.type === 'code')
          .forEach((block) => block.state.error = null);
    },

    /**
     * To be called when an error occurs during code execution
     * Highlights the code where the error occurred.
     *
     * @param {string} error  The error message
     * @param {number} errorBeginIndex  The begin of the erroneous code
     * @param {number} errorEndIndex  The end of the erroneous code
     */
    executeError: function(error, errorBeginIndex, errorEndIndex) {
      if (error === 'Hit front/end of notebook') {
        return;
      }

      const coqState = this.coq.getState();

      // make sure the error interval is exactly one sentence
      const sentence = coqState.sentenceAfterIndex(this.executedIndex);

      if (sentence === null) {
        if (coqState.sentenceSize() > 0) {
          errorBeginIndex = coqState.beginIndexOfSentence(0);
          errorEndIndex = coqState.endIndexOfSentence(0);
        } else {
          errorBeginIndex = 0;
          errorEndIndex = this.coqCode.length - 1;
        }
      } else {
        const s = sentence.sentence;
        errorBeginIndex = s.beginIndex;
        errorEndIndex = s.endIndex;
      }

      // Also clear errors
      this.notebook.blocks
          .filter((block) => block.type === 'code')
          .forEach((block) => block.state.error = null);

      let index = 0;
      for (const block of this.notebook.blocks) {
        if (block.type !== 'code') {
          continue;
        }

        // Add the underline for each block that overlaps with the error
        // Also add the error message to the last block with the error
        const blockStart = index;
        const blockEnd = index + block.text.length;
        if (blockStart < errorEndIndex && blockEnd > errorBeginIndex) {
          // this block overlaps with the error
          block.state.error = {
            from: Math.max(errorBeginIndex - index, 0),
            to: Math.min(errorEndIndex - index, block.text.length),
          };
        }
        if (blockEnd >= errorEndIndex) {
          const longError =
              error.match(/In environment[\s\S]*Unable to unify([\s\S]*)$/);
          if (longError != null) {
            error = 'Unable to unify ' + longError[1];
          }
          block.state.error.message = error;
          break;
        }
        index += block.text.length + 1;
      }

      const sn = coqState.sentenceBeforeIndex(errorBeginIndex - 1);
      this.executedIndex = sn >= 0 ? coqState.endIndexOfSentence(sn) : -1;
    },

    /**
     * Adds a message to the messages panel
     *
     * @param {string} message  The message to be added
     * @param {Number} sentenceId The associated sentence id of the
     *    message or null
     */
    message: function(message, sentenceId) {
      this.eventBus.$emit('on-coq-message', {text: message, id: sentenceId});
    },

    findAndReplace: function() {
      this.showFind = !this.showFind;
      if (this.showFind) {
        this.$nextTick(()=> {
          this.$refs.editWindow.$refs.find.$refs.findInput.focus();
        });
      }
    },

    toggleFocusInputs: function() {
      // Toggle grading mode
      if (this.notebook.exerciseSheet === true) {
        this.focusInputs = !this.focusInputs;

        const editables=document.getElementsByClassName('edit-block');
        const len=editables.length;

        for (let i=0; i<len; i++) {
          if (this.focusInputs) {
            editables[i].classList.add('highlight-mode');
          } else {
            editables[i].classList.remove('highlight-mode');
          }
        }
      }
    },

    nextInput: function() {
      const currentScroll = this.$refs.editWindow.$el.scrollTop;
      const inputs =
          this.$refs.editWindow.$el.getElementsByClassName('input-start-block');

      if (inputs.length > 0) {
        for (let i = 0; i < inputs.length; i++) {
          const offset = inputs[i].offsetTop;
          // Need this offset, as setting scroll to x changes it to x-epsilon
          if (currentScroll + 1.0 < offset) {
            this.$refs.editWindow.$el.scrollTop = offset;
            return;
          }
        }

        // By deduction if we get here we are past the last input block
        // this.$refs.editWindow.$el.scrollTop = inputs[0].offsetTop;
      }
    },

    previousInput: function() {
      const currentScroll = this.$refs.editWindow.$el.scrollTop;
      const inputs =
          this.$refs.editWindow.$el.getElementsByClassName('input-start-block');

      if (inputs.length > 0) {
        for (let i = inputs.length-1; i >= 0; i--) {
          const offset = inputs[i].offsetTop;
          if (currentScroll > offset) {
            this.$refs.editWindow.$el.scrollTop = offset;
            return;
          }
        }

        // By deduction if we get here we are past the first input block
        // this.$refs.editWindow.$el.scrollTop =
        //     inputs[inputs.length-1].offsetTop;
      }
    },

    clearErrors: function(cm, index) {
      let checkIndex = 0;
      for (const block of this.notebook.blocks) {
        if (block.type !== 'code') {
          continue;
        }

        if ((checkIndex + block.text.length + 1) <= index) {
          block.state.error = null;
        } else {
          break;
        }
        checkIndex += block.text.length + 1;
      }

      const line = cm.posFromIndex(index).line;
      const marks = cm.findMarks({line, ch: 0}, {line: line + 1, ch: 0});
      marks.map((mark) => mark.clear());

      const widgets = cm.lineInfo(line).widgets;
      if (widgets) {
        widgets.map((widget) => widget.clear());
      }
    },

    /**
     * Inserts the specified text at the cursor position
     * and gives the editor focus again.
     *
     * @param {string} toInsert  The text to insert
     */
    insertAtCursor: function(toInsert) {
      const cm = this.$refs.editWindow.$refs.codeMirrors[0].codemirror;
      cm.replaceRange(toInsert, cm.getCursor());
      cm.focus();
    },

    updateButtons: function() {
      const args = {
        notebook: this.notebook,
        ready: this.ready,
      };
      this.$emit('update-buttons', this.index, args);
    },

    forwardEvent: function(event) {
      if (event.payload != null) {
        this.eventBus.$emit(event.event, event.payload);
      } else {
        this.eventBus.$emit(event.event);
      }
    },
  },
  mounted: function() {
    this.eventBus.$on('notebook-state-changed', this.updateButtons);
    this.eventBus.$on('changeMultipleInputs', this.changeMultipleInputs);
    this.eventBus.$on('undo', this.undo);
    this.eventBus.$on('redo', this.redo);
    this.eventBus.$on('insertAtCursor', this.insertAtCursor);
    this.eventBus.$on('changeInput', this.changeInput);
    this.eventBus.$on('setCursorPos', this.setCursorPos);
    this.eventBus.$on('toggleFocusInputs', this.toggleFocusInputs);
    this.eventBus.$on('nextInput', this.nextInput);
    this.eventBus.$on('previousInput', this.previousInput);
    this.eventBus.$on('findAndReplace', this.findAndReplace);
    this.eventBus.$on('saveFile', this.saveFile);
    this.eventBus.$on('saveAsFile', this.saveAsFile);
    this.eventBus.$on('exportToCoq', this.exportToCoq);
    this.eventBus.$on('exportToExerciseSheet', this.exportToExerciseSheet);
    this.eventBus.$on('compilewplib', this.compilewplib);
    this.eventBus.$on('close', this.close);

    const noParamCoqEvent = (name) => {
      return () => {
        writeActivity('coq-exec-' + name, {
          file: this.notebook.filePath,
        });
      };
    };

    this.eventBus.$on('coqNext', noParamCoqEvent('next'));
    this.eventBus.$on('coqPrev', noParamCoqEvent('prev'));
    this.eventBus.$on('coqAll', noParamCoqEvent('all'));
    this.eventBus.$on('coqToCursor', () => {
      writeActivity('coq-exec-to-cursor', {
        targetIndex: this.findCodeIndex(),
        file: this.notebook.filePath,
      });
    });
    this.eventBus.$on('coqTo', (index) => {
      writeActivity('coq-exec-to', {
        targetIndex: index,
        file: this.notebook.filePath,
      });
    });

    // When the proofwindow is mounted, update to disable all the buttons that
    // require a notebook to be opened
    this.updateButtons();

    // remove links from tabs to stop middle mouse clicks
    setTimeout(() => {
      const list = document.getElementsByClassName('nav-link');
      for (let i = 0; i<list.length; i++) {
        list[i].removeAttribute('href');
      }
    }, 0);
  },
};

</script>


<style lang="scss">
  @import '../../assets/sass/_colors.scss';

  .proof-and-side-window {
    width: 100%;
    display: flex;
    height: inherit;
    flex-direction: row;

    .proof-window {
      width: 100%;
      display: flex;
      height: inherit;
      flex-direction: row;

      @include respond-to(sm-lower) {
        flex-direction: column;
      }
    }

    .side-window {
      @include theme(background-color, color-gray-light);
    }
  }

  .executeError {
    text-decoration: red underline;
  }

  .error-message {
    @include theme(background-color, color-error-message);
    padding: 5px;
  }

  a.nav-link {
    cursor: pointer;
  }

</style>
