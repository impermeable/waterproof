<template>
  <div class="topbar">
    <div class="button-container">
      <img src="../../../assets/images/WaterproofIconWhite.svg"
          @click='eventBus.$emit("goto-homescreen")'
           alt="logo" class="top-icon" />

      <b-dropdown id="file-dropdown"
                  text="File"
                  class="topbar-dropdown"
                  no-caret>
        <topbar-button
                       v-for="button in topbarButtons['file']"
                       v-bind:buttonInfo="button"
                       v-bind:shortKeys="shortKeys"
                       v-bind:key="button.text"
                       v-bind:event-bus="eventBus"
        />
        <topbar-button
                       v-for="button in fileList"
                       v-bind:buttonInfo="button"
                       v-bind:shortKeys="shortKeys"
                       v-bind:key="button.text"
                       v-bind:event-bus="eventBus"
        />
      </b-dropdown>
      <b-dropdown id="edit-dropdown"
                  text="Edit"
                  class="topbar-dropdown"
                  no-caret>
        <topbar-button
                       v-for="button in topbarButtons['edit']"
                       v-bind:buttonInfo="button"
                       v-bind:shortKeys="shortKeys"
                       v-bind:key="button.text"
                       v-bind:event-bus="eventBus"
        />
      </b-dropdown>
      <b-dropdown id="coq-dropdown"
                  text="Coq"
                  class="topbar-dropdown"
                  no-caret>
        <topbar-button
                       v-for="button in topbarButtons['coq']"
                       v-bind:buttonInfo="button"
                       v-bind:shortKeys="shortKeys"
                       v-bind:key="button.text"
                       v-bind:event-bus="eventBus"
        />
      </b-dropdown>
      <b-dropdown id="help-dropdown"
                  text="Help"
                  class="topbar-dropdown"
                  no-caret>
        <topbar-button
                       v-for="button in topbarButtons['help']"
                       v-bind:buttonInfo="button"
                       v-bind:shortKeys="shortKeys"
                       v-bind:key="button.text"
                       v-bind:event-bus="eventBus"
        />
      </b-dropdown>
    </div>
    <SearchBar :event-bus="eventBus"/>
  </div>
</template>

<script>
import TopbarButton from './TopbarButton';
import SearchBar from '../assistance/search/SearchBar';
import {DropdownPlugin} from 'bootstrap-vue/src/index';

import Vue from 'vue';
import Recents from '../../../io/recents';

Vue.use(DropdownPlugin);

export default {
  name: 'Topbar',
  props: {
    shortKeys: Object,
    eventBus: Vue,
    recents: Recents,
  },
  components: {
    TopbarButton,
    SearchBar,
  },
  data: function() {
    return {
      topbarButtons: {
        file: [
          {
            text: 'New',
            event: 'openNewTab',
            eventType: 'on-edit',
            shortkeyTag: 'newFile',
          },
          {
            text: 'Open',
            event: 'loadFile',
            eventType: 'on-edit',
            shortkeyTag: 'loadFile',
          },
          {
            text: 'Save',
            event: 'saveFile',
            eventType: 'on-proof-window',
            shortkeyTag: 'saveFile',
            requires: ['notebook'],
          },
          {
            text: 'Save as',
            event: 'saveAsFile',
            eventType: 'on-proof-window',
            shortkeyTag: 'saveAsFile',
            line: 'true',
            requires: ['notebook'],
          },
          {
            text: 'Export to Coq file',
            event: 'exportToCoq',
            eventType: 'on-proof-window',
            shortkeyTag: 'exportToCoq',
            requires: ['notebook'],
          },
          {
            text: 'Import from Coq file',
            event: 'importFromCoq',
            eventType: 'on-edit',
            shortkeyTag: 'importFromCoq',
          },
          {
            text: 'Export to exercise sheet',
            event: 'exportToExerciseSheet',
            eventType: 'on-proof-window',
            shortkeyTag: 'exportToExerciseSheet',
            line: 'true',
            requires: ['notebook', 'no-exercise-sheet'],
          },
          {
            text: 'Compile waterproof libraries',
            event: 'compilewplib',
            eventType: 'on-proof-window',
            line: 'true',
          },
          {
            text: 'Close tab',
            event: 'close',
            eventType: 'on-proof-window',
            shortkeyTag: 'closeTab',
            line: true,
            requires: ['notebook'],
          },
        ],
        edit: [
          {
            text: 'Undo',
            event: 'undo',
            eventType: 'on-proof-window',
            shortkeyTag: 'undo',
            requires: ['notebook'],
          },
          {
            text: 'Redo',
            event: 'redo',
            eventType: 'on-proof-window',
            shortkeyTag: 'redo',
            line: 'true',
            requires: ['notebook'],
          },
          {
            text: 'Find in notebook',
            event: 'findAndReplace',
            eventType: 'on-proof-window',
            shortkeyTag: 'findAndReplace',
            line: 'true',
            requires: ['notebook'],
          },
          {
            text: 'Insert text block',
            event: 'insertText',
            eventType: 'on-proof-window',
            shortkeyTag: 'insertText',
            requires: ['notebook'],
          },
          {
            text: 'Insert code block',
            event: 'insertCode',
            eventType: 'on-proof-window',
            shortkeyTag: 'insertCode',
            requires: ['notebook'],
          },
          {
            text: 'Insert hint',
            event: 'insertHint',
            eventType: 'on-proof-window',
            shortkeyTag: 'insertHint',
            requires: ['notebook', 'no-exercise-sheet'],
          },
          {
            text: 'Insert input',
            event: 'insertInputArea',
            eventType: 'on-proof-window',
            shortkeyTag: 'insertInputArea',
            requires: ['notebook', 'no-exercise-sheet'],
          },
        ],
        coq: [
          {
            text: 'Execute next',
            event: 'coqNext',
            eventType: 'on-proof-window',
            shortkeyTag: 'executeNext',
            requires: ['notebook', 'coq-ready'],
          },
          {
            text: 'Execute previous',
            event: 'coqPrev',
            eventType: 'on-proof-window',
            shortkeyTag: 'executePrev',
            requires: ['notebook', 'coq-ready'],
          },
          {
            text: 'Execute to cursor',
            event: 'coqTo',
            eventType: 'on-proof-window',
            shortkeyTag: 'executeToCursor',
            requires: ['notebook', 'coq-ready'],
          },
          {
            text: 'Execute all',
            event: 'coqAll',
            eventType: 'on-proof-window',
            shortkeyTag: 'executeAll',
            requires: ['notebook', 'coq-ready'],
            line: process.env.NODE_ENV !== 'production',
          },
        ].concat(process.env.NODE_ENV !== 'production' ? [
          {
            text: 'Enable logging',
            event: 'coqLog',
            eventType: 'on-proof-window',
            shortkeyTag: '',
            requires: ['notebook', 'coq-ready'],
          },
          {
            text: 'Enable timing',
            event: 'coqTime',
            eventType: 'on-proof-window',
            shortkeyTag: '',
            requires: ['notebook', 'coq-ready'],
          },
        ] : []),
        help: [
          // 0,1,2 are magical constants from store.js
          {
            text: 'Common Coq commands',
            event: {
              method: 'toggleCommon',
              detail: 3,
            },
            eventType: 'on-edit',
            shortkeyTag: 'commonCommands',
          },
          {
            text: 'Common mathematical symbols',
            event: {
              method: 'toggleCommon',
              detail: 2,
            },
            eventType: 'on-edit',
            shortkeyTag: 'commonSymbols',
          },
          {
            text: 'Common Coq tactics',
            event: {
              method: 'toggleCommon',
              detail: 1,
            },
            eventType: 'on-edit',
            shortkeyTag: 'commonTactics',
            line: 'true',
          },
          {
            text: 'Tutorial',
            event: 'openTutorial',
            eventType: 'on-edit',
            shortkeyTag: 'tutorialPage',
          },
          {
            text: 'About',
            event: 'openAboutPage',
            eventType: 'on-edit',
            shortkeyTag: '',
          },
        ],
      },
    };
  },
  computed: {
    fileList: function() {
      const list = [];
      for (let i = 0; i < Math.min(this.recents.filelist.length, 5); i++) {
        const item = this.recents.filelist[i];
        list.push({
          text: item.name,
          event: {
            method: 'openTab',
            detail: item.location,
          },
          eventType: 'on-edit',
          shortkeyTag: '',
        },
        );
      }
      return list;
    },
  },
  mounted: function() {
    this.eventBus.$on('notebook-opened', this.updateButtons);
  },
  methods: {
    updateButtons: function(status) {
      for (const name in this.topbarButtons) {
        if (Object.prototype.hasOwnProperty.call(this.topbarButtons, name)) {
          const buttonSection = this.topbarButtons[name];
          for (const button of buttonSection) {
            if (button.requires === undefined) {
              Vue.set(button, 'disabled', false);
              continue;
            }
            const isEnabled = button.requires.every(
                (requirement) => status.includes(requirement)
            );
            this.$set(button, 'disabled', !isEnabled);
          }
        }
      }
    },
  },
};

</script>

<style lang="scss">
  .show > .btn-secondary.dropdown-toggle {
    background-color: $color-primary-dark!important;
    border: none;
  }
</style>
