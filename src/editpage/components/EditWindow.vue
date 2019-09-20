<template>
  <div class="edit-window" ref="domEl" :id="'edit-window-' + tabindex"
      @contextmenu="openContextMenu($event)">
    <Gutter :ani="ani" ref="execGutter" :height="gutterHeight"
            :exec-height="execHeight"
            :exec-height-ball="execHeightBall" :executed="executed"/>
    <div ref="editPane"
        class="edit-pane"
        @click.self="onClick"
        @paste="paste">
      <inter-block
          :key="'interblock-' + 0"
          :block="null" :exercise="exercise"
          :active="selectedInterblock === 0"
          :wide="true"
          :index="0">
      </inter-block>
      <template v-for="(block, index) in blocks">
        <component v-show="!block.state.foldStatus.isFolded"
                  :is="toComponent(block.type)" :block="block"
                  :key="block.type + index" :index="index"
                  :exercise="exercise" :event-bus="eventBus">
        </component>
        <fold-block v-if="block.state.foldStatus.startFold"
                    :key="block.type + index + '+'"
                    :event-bus="eventBus"
                    :block="block" :index="index"
                    :exercise="exercise"></fold-block>
        <div v-if="index === focusedElement"
            :key="'holder-' + index " class="edit-holder"
            :class="{floatyEditor: floating}">
          <codemirror id="source-editor" :key="'editor' + index"
                  class="edit-text" :value="block.text"
                  :options="getCMOptions(block.type)"
                  @ready="onCmReady" @changes="onChanges"
                  @keyHandled="keyup" @cursorActivity="cursorMove"
                  ref="codeMirrors">
          </codemirror>
          <!-- Placeholder for toggling the assistance bar -->
          <div v-if="block.type === 'code'"
            @click="toggleAssistanceBar"
            class="toggle-bar">
          </div>
          <assistance-bar v-show="isShowingAssistance"
            v-if="block.type === 'code'"
            :event-bus="eventBus">
          </assistance-bar>
        </div>

        <inter-block :key="'interblock-' + index + 1"
            :block="block" :exercise="exercise"
            :active="selectedInterblock === index + 1"
            :wide="block.start"
            :index="index + 1">
        </inter-block>

      </template>
      <find ref="find" v-show="showFind"
            :event-bus="eventBus"
            v-bind:blocks="blocks" v-bind:exercise="exercise" />
    </div>
    <block-context-menu ref="menu"
        :event-bus="eventBus" :blocks="blocks" :shortKeys="shortKeys">
    </block-context-menu>
  </div>
</template>

<script>
import {codemirror} from 'vue-codemirror';
import 'codemirror/lib/codemirror.css';
import 'codemirror/addon/display/placeholder';
import 'codemirror/addon/search/searchcursor';
import debounce from 'lodash.debounce';

import CodeBlock from './blocks/CodeBlock';
import TextBlock from './blocks/TextBlock';
import HintBlock from './blocks/HintBlock';
import InputBlock from './blocks/InputBlock';
import FoldBlock from './blocks/FoldBlock';
import InterBlock from './blocks/InterBlock';
import CoqInterface from '../../coq/CoqInterface';
import BlockContextMenu from './blocks/BlockContextMenu';
import AssistanceBar from './assistance/AssistanceBar';
import Find from './Find';
import Gutter from './Gutter';
import CodeExecution from './mixins/CodeExecution';
import CodeMirrorHandler from './mixins/CodeMirrorHandler';

export default {
  name: 'EditWindow',
  mixins: [CodeExecution, CodeMirrorHandler],
  components: {
    codemirror,
    Gutter, Find,
    TextBlock, CodeBlock, HintBlock, InputBlock, FoldBlock, InterBlock,
    BlockContextMenu, AssistanceBar,
  },
  props: {
    index: Number,
    coq: CoqInterface,
    targetIndex: Number,
    blocks: Array,
    exercise: Boolean,
    debug: Boolean,
    showFind: Boolean,
    shortKeys: Object,
    tabindex: Number,
    eventBus: Object,
  },
  data: function() {
    return {
      testValue: 'Proof.',
      floating: false,
      executed: false,
      nextCursorPos: -1,
      execHeight: 0,
      execHeightBall: 0,
      gutterHeight: 100,
      timer: null,
      executedUpTo: null,
      pendingUpTo: null,
      cursorPos: null,
      isShowingAssistance: true,
      ani: true,
      focusedElement: -1,
      dispatchTextChange: debounce((type, blockIndex, newValue) => {
        // Don't update the block text yet. This is done in proofwindow so it
        // can detect the changes to allow undoing them
        this.eventBus.$emit('changeInput', type, blockIndex, newValue);
      }, 250, {leading: true, maxWait: 2500, trailing: true}),
      selectedInterblock: -1,
    };
  },
  mounted: function() {
    // setTimeout is called after dom completes
    setTimeout(() => this.setGutterHeight(), 0);
    this.eventBus.$on('set-focus', this.setFocusedElement);
  },
  methods: {
    onChanges: function(cm) {
      const value = cm.getValue();

      this.dispatchTextChange('input', this.focusedElement, value);
      this.refreshExecStatus(false);
    },
    toComponent: function(type) {
      if (type === 'code') {
        return 'code-block';
      } else if (type === 'hint') {
        return 'hint-block';
      } else if (type === 'input') {
        return 'input-block';
      } else {
        return 'text-block';
      }
    },
    setFocusedElement: function(index, find = false) {
      if (this.focusedElement === index) {
        // If we click again on the element that already has focus, it should
        // already have a CodeMirror open. So, we make sure to just focus on it
        if (this.$refs.codeMirrors && this.$refs.codeMirrors.length === 1) {
          this.$refs.codeMirrors[0].codemirror.focus();
          return;
        }
      }
      this.selectedInterblock = -1;
      if (this.focusedElement !== -1) {
        const isAfterSource = index > this.focusedElement;
        if (this.blurSource() && isAfterSource) {
          index--;
        }
      }

      this.$refs.find.changeFocusedElement(index, find);
      this.focusedElement = index;
      this.refreshExecStatus(false);
    },
    setFocusedInterblock: function(index) {
      const isAfterSource = index > this.focusedElement;
      if (this.blurSource() && isAfterSource) {
        index--;
      }
      this.selectedInterblock = index;
    },
    blurSource: function() {
      this.selectedInterblock = -1;

      if (this.focusedElement === -1 ||
          this.focusedElement >= this.blocks.length) {
        this.focusedElement = -1;
        this.cursorPos = {block: this.focusedElement};
        this.eventBus.$emit('setCursorPos', this.cursorPos);
        return false;
      }

      this.dispatchTextChange.flush();

      let removed = false;

      if (this.blocks[this.focusedElement].text === '') {
        removed = true;
        this.dispatchTextChange(
            'remove-block',
            this.focusedElement,
            null,
            this
        );
        this.dispatchTextChange.flush();
      }

      this.focusedElement = -1;
      this.cursorPos = {block: this.focusedElement};
      this.eventBus.$emit('setCursorPos', this.cursorPos);

      this.$refs.find.currentCm = null;

      this.refreshExecStatus(false);

      return removed;
    },

    // blurCM: function() {
    //   document.querySelector('.CodeMirror-cursors')
    //       .style.visibility = 'visible';
    // },
    onCmReady: function(cm) {
      let cursorPos = this.nextCursorPos;
      if (cursorPos < 0) {
        cursorPos = cm.getValue().length;
      }
      cm.setCursor(cm.posFromIndex(cursorPos));
      this.cursorMove(cm);

      cm.focus();
      this.$refs.find.currentCm = cm;
      this.$refs.find.onCodeMirrorReady();
      this.$refs.find.onCodeMirrorReady = () => {};

      cm.on('paste', this.cmPaste);
    },
    moveSelection: function(event) {
      if (event.srcKey === 'Right' || event.srcKey === 'Down') {
        for (let i = this.selectedInterblock; i < this.blocks.length; i++) {
          if (this.isEditableBlock(this.blocks[i])) {
            this.setFocusedElement(i);
            this.$nextTick(() => {
              this.$refs.codeMirrors[0].codemirror.execCommand('goDocStart');
            });
            break;
          }
        }
      } else if (this.selectedInterblock > 0 &&
          !this.blocks[this.selectedInterblock - 1].start) {
        this.setFocusedElement(this.selectedInterblock - 1);
      }
    },
    keyup: function(cm, key, event) {
      if (event.shiftKey ||
          !(key.includes('Right')
            || key.includes('Left')
            || key.includes('Up')
            || key.includes('Down'))) {
        return;
      }

      const cursorIndex = cm.indexFromPos(this.cursorPos.from);
      const cursorLine = this.cursorPos.line;

      if (key.includes('Right') && cursorIndex === cm.getValue().length
          || key.includes('Down') && cursorLine === cm.lineCount() - 1) {
        this.setFocusedInterblock(this.focusedElement + 1);
      } else if (key.includes('Left') && cursorIndex === 0
          || key.includes('Up') && cursorLine === 0) {
        for (let i = this.focusedElement - 1; i >= 0; i--) {
          if (this.blocks[i].type === 'input' && this.blocks[i].start
              || this.isEditableBlock(this.blocks[i])) {
            this.setFocusedInterblock(i + 1);
            return;
          }
        }
        if (!this.exercise) {
          this.setFocusedInterblock(0);
        }
      }
    },
    isEditableBlock: function(block) {
      const skippedTypes = ['input'];
      return !skippedTypes.includes(block.type)
          && (!this.exercise || block.state.inInputField);
    },
    toggleAssistanceBar() {
      this.isShowingAssistance = !this.isShowingAssistance;
    },
    findCodeIndex(index, clamp) {
      if (index < 0) {
        return null;
      }
      let len = 0;
      let lastCodeBlock = -1;
      for (let i = 0; i < this.blocks.length; i++) {
        const block = this.blocks[i];
        if (block.type !== 'code') {
          continue;
        }
        lastCodeBlock = i;
        const newLen = len + block.text.length + 1;
        if (newLen > index) {
          return {blockIndex: i, posInBlock: index - len};
        }
        len = newLen;
      }
      if (clamp) {
        const block = this.blocks[lastCodeBlock];
        const posInBlock = block.text.length;
        return {blockIndex: lastCodeBlock, posInBlock};
      } else {
        return null;
      }
    },
    clearCodeDecorations() {
      for (const block of this.blocks) {
        if (block.type !== 'code') {
          continue;
        }

        // Clear the execution but not the error state
        block.state.executedUpTo = -1;
      }
    },
    /**
     * Changes height of gutter to the height of the editpane,
     * adds 100 px as well for 'overleaf-scrolling'
     */
    setGutterHeight: function() {
      const editPane = this.$refs.editPane;
      this.gutterHeight = editPane.scrollHeight + 100;
    },
    alignGutter: function(animation = true) {
      this.ani = animation;

      // Set the gutter height to equal content height
      this.setGutterHeight();

      const tick = this.$refs.editPane.querySelector('.exec-inline-tick');

      if (tick != null) {
        const rect = tick.getBoundingClientRect();
        const editPane = this.$refs.editPane;
        const rect2 = editPane.getBoundingClientRect();

        this.execHeight = (rect.bottom + rect.top) / 2 - rect2.top - 10;
        this.execHeightBall = rect.top - rect2.top;
      }

      if (!animation) {
        setTimeout(() => {
          this.ani = true;
        }, 50);
      }
    },
    openContextMenu: function(event) {
      this.$refs.menu.open(event);
    },
    paste: function(event) {
      this.$refs.menu.paste(event);
    },
    cmPaste: function(cm, event) {
      this.paste(event);
    },
    onClick: function() {
      this.$refs.find.resetFind();
      this.blurSource();
    },
  },
  watch: {
    'index': function(newIndex) {
      if (!newIndex) {
        newIndex = 0;
        this.pendingUpTo = 0;
      }
      this.executedUpTo = newIndex;

      this.pendingUpTo = this.pendingUpTo
          && Math.max(this.pendingUpTo, newIndex);
      this.refreshExecStatus(true);
    },

    'targetIndex': function(newIndex) {
      this.pendingUpTo = newIndex || 0;
      this.refreshExecStatus(true);
    },

  },
  /**
   * Checks if DOM elements are changed and if so,
   * sets the gutter height accordingly.
   */
  beforeUpdate: function() {
    this.setGutterHeight();
  },
};
</script>

<style lang="scss">
  @import "../../assets/stylesheets/edit.scss";

#source-editor {
  width: 100%;
  border: 1px solid black;
}


.CodeMirror-placeholder {
  color: gray !important;
}

.edit-window {
  flex: 1 0 50%;
  position: relative;
  padding: 5px;
  overflow-y: scroll;
  min-height: 50%;
}


.highlightText {
  background-color: $color-primary-extra-light;
}

.edit-holder {
  position: relative;
  margin: 4px 0;
  width: calc(100% - 16px);
}

.edit-window {
  display: flex;
}

.edit-pane {
  width: calc(100% - 40px);
}

.no-transition {
  transition: none !important;
}

.toggle-bar {
  background-color: $color-primary-dark;
  height: 5px;
}

</style>
