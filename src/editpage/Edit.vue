<template>
  <div class="container-fluid" id="app">
    <topbar v-bind:shortKeys="shortKeys" :eventBus="mainBus" :recents="recents">
    </topbar>
    <div class="content">
      <sidebar v-bind:shortKeys="shortKeys" :eventBus="mainBus">
      </sidebar>

      <b-tabs ref="tabs" no-fade no-key-nav no-nav-style
        active-nav-item-class="tab-active"
        active-tab-class="tab-content-active"
        @input="switchToTab"
      >
        <proof-window
          v-for="(tab, index) in tabs"
          v-bind:key="tab.id"
          :uri="tab.fileURI"
          :index="index"
          :debug="debug"
          :socket="socket"
          :shortKeys="shortKeys"
          ref="proofWindow"
          @update-buttons="updateButtons"
          ></proof-window>

          <!-- New Tab Button (Using tabs slot) -->
          <template slot="tabs-end">
            <button class="new-tab-button" @click="openNewTab">+</button>
            <button style="display:none;"
              v-shortkey="closeTabShortKey"
              @shortkey="closeCurrentTab"
              @click="closeCurrentTab">
            </button>
          </template>

          <!-- Render this if no tabs -->
          <div slot="empty" class="text-center text-muted">
            There are no open notebooks<br>
            Open a new notebook or open an existing one using the buttons above.
          </div>
      </b-tabs>
    </div>
    <div>
      <b-modal id="about-modal" scrollable title="About Waterproof" hide-footer>
        <about/>
      </b-modal>
    </div>
  </div>
</template>

<script>
import About from './components/About';
import ProofWindow from './components/ProofWindow';
import Sidebar from './components/menubars/Sidebar';
import Topbar from './components/menubars/Topbar';
import ShortKeys from '../io/shortKey.js';

import Vue from 'vue';
import 'bootstrap/dist/css/bootstrap.css';
import 'bootstrap-vue/dist/bootstrap-vue.css';
import {TabsPlugin, ModalPlugin} from 'bootstrap-vue';

import Recents from '../io/recents';
import TCPManager from '../coq/serapi/workers/TCPManager';

Vue.use(TabsPlugin);
Vue.use(ModalPlugin);

export default {
  name: 'app',
  components: {
    About,
    ProofWindow,
    Sidebar,
    Topbar,
  },
  data: function() {
    return {
      recents: new Recents(),
      debug: false,
      currentTab: 0,
      tabs: [],
      tabIdCounter: 0,
      socket: null,
      shortKeys: new ShortKeys(),
      mainBus: new Vue,
    };
  },
  computed: {
    currentProofWindow: function() {
      if (this.$refs.proofWindow === undefined) {
        return null;
      }
      return this.$refs.proofWindow[this.currentTab];
    },
    closeTabShortKey: function() {
      return this.shortKeys.shortKeys['closeTab'];
    },
  },
  methods: {
    updateButtons: function(index, args, check=true) {
      if (check) {
        // If check is true, we only update the sidebar if the relevant proof-
        // window is active. This is set to false when switching between tabs
        // to avoid timing issues
        if (this.currentTab !== index) {
          return;
        }
      }
      let notebook = null;
      let ready = null;
      if (args) {
        notebook = args.notebook;
        ready = args.ready;
      }
      const status = [];
      // First find out whether a notebook is opened, if so, if it is an
      // sheet, whether Coq is ready to execute, etc.
      if (ready) {
        status.push('coq-ready');
      }
      if (notebook) {
        status.push('notebook');
        if (notebook.exerciseSheet) {
          status.push('exercise-sheet');
        } else {
          status.push('no-exercise-sheet');
        }
      }
      this.mainBus.$emit('notebook-opened', status);
    },

    /**
     * Changes the currently opened tab to the indicated tab
     *
     * @param {number} id  The index of the tab to which should be switched
     * @param {boolean} updateGutter  Whether the gutter containing
     *   the execution status should also be updated
     */
    switchToTab: function(id, updateGutter = true) {
      const pw = this.$refs.proofWindow[id];
      const args = pw ? {
        notebook: pw.notebook,
        ready: pw.ready,
      } : {
        notebook: null,
        ready: false,
      };
      this.updateButtons(id, args, false);
      if (id < 0) {
        return;
      }
      this.$refs.tabs.currentTab = id;
      this.currentTab = id;
      if (updateGutter) {
        this.$refs
            .proofWindow[this.currentTab]
            .$refs
            .editWindow
            .refreshExecStatus(false);
      }
    },

    /**
     * Either opens a new tab with the specified notebook and
     * switches to this tab if the notebook is not opened yet,
     * otherwise it switches to the tab where the notebook is opened.
     * When fileURI is null, it opens a new empty notebook
     *
     * @param {string} fileURI  The URI of the file to be opened
     */
    openTab: function(fileURI) {
      // Check if this tab is already opened somewhere
      // (only if the URI is non-null, because multiple new tabs should still
      // be possible)
      const duplicateIndex = fileURI === null ? -1 : this.tabs.findIndex(
          (tab) => tab.fileURI === fileURI
      );
      if (duplicateIndex >= 0) {
        this.switchToTab(duplicateIndex);
        return;
      }
      const newId = this.tabs.length;
      this.tabs.push({
        fileURI: fileURI,
        id: this.tabIdCounter++,
      });
      this.switchToTab(newId, false);
      if (fileURI !== null) {
        this.recents.addFileListEntry(fileURI);
      }
    },

    /**
     * Opens a tab with a new empty notebook, and switches to this tab
     */
    openNewTab: function() {
      this.openTab(null);
    },

    /**
     * Opens a tab containing the tutorial.
     * This needs to be a separate method for the buttons on
     * the edit page to work.
     */
    openTutorial: function() {
      this.openTab('Tutorial');
    },

    /**
     * Closes the specified tab. If there are still unsaved changes,
     * a dialog asking confirmation is first shown.
     * If there are no other opened tabs, a new empty tab is created.
     *
     * @param {number} id  The id of the tab that should be closed
     * @return {boolean} true if the tab closed successfully,
     *   false if the user prevented this using the dialog
     */
    closeTab: function(id) {
      if (this.$refs.proofWindow[id].notebook &&
          this.$refs.proofWindow[id].notebook.unsavedChanges) {
        const {dialog} = require('electron').remote;

        const dialogOptions = {type: 'info', title: 'Waterproof',
          buttons: ['Yes', 'Cancel'],
          message: 'This tab contains unsaved changes, ' +
          'are you sure you want to close it?',
        };

        // index in buttons
        const result = dialog.showMessageBox(dialogOptions);
        if (result === 1) {
          return false;
        }
      }
      // If this is the last tab that is still opened, we make sure to keep a
      // single empty tab open. This is the same behaviour as some other
      // programs, such as Notepad++
      if (this.tabs.length === 1) {
        id = 0;
        this.openTab(null);
      }
      this.tabs.splice(id, 1);
      if (this.currentTab > id) {
        this.switchToTab(this.currentTab - 1);
      }
      return true;
    },

    /**
     * Closes the currently active tab. If there are still unsaved changes,
     * a dialog asking confirmation is first shown.
     * If there are no other opened tabs, a new empty tab is created.
     *
     * @return {boolean} true if the tab closed successfully,
     *   false if the user prevented this using the dialog
     */
    closeCurrentTab: function() {
      return this.closeTab(this.currentTab);
    },

    /**
     * Sets the URI of the specified tab to the specified URI.
     *
     * @param {number} index index of tab of which URI must be set
     * @param {string} fileURI The URI that should be set
     */
    setTabURI: function(index, fileURI) {
      this.tabs[index].fileURI = fileURI;
      console.log(this.tabs);
    },

    /**
     * Shows a dialog for selecting a file to open in waterproof,
     * opens all the selected files, and adds them to the list of recent files
     */
    loadFile: function() {
      const options = {
        filters: [
          {
            name: 'Waterproof files',
            extensions: ['wpn', 'wpe'],
          },
          {
            name: 'Waterproof notebooks',
            extensions: ['wpn'],
          },
          {
            name: 'Waterproof exercise',
            extensions: ['wpe'],
          },
          {
            name: 'All files',
            extensions: ['*'],
          },
        ],
        properties: ['openFile'],
      };

      const {dialog} = require('electron').remote;
      const filePaths = dialog.showOpenDialog(options);

      if (filePaths) {
        for (const file of filePaths) {
          this.openTab(file);
          this.addToRecentFileList(file);
        }
      }
    },

    /**
     * Shows a dialog for selecting a coq file to open in waterproof,
     * exports all selected files to waterproof notebooks, and opens them all
     */
    importFromCoq: function() {
      const options = {
        title: 'Import from Coq file',
        properties: ['openFile'],
        filters: [
          {
            name: 'Coq file',
            extensions: ['v'],
          },
          {
            name: 'All files',
            extensions: ['*'],
          },
        ],
      };

      const {dialog} = require('electron').remote;
      const filename = dialog.showOpenDialog(options);
      if (filename) {
        this.tabs[this.currentTab].fileURI = null;
        this.$nextTick(() => {
          this.currentProofWindow.notebook.importFromCoq(filename[0]);
        });
      }
    },

    /**
     * Returns to the homepage of the application.
     * If there are unsaved changes in any of the tabs, it first asks
     * the user for confirmation via a dialog.
     */
    homeScreen: function() {
      const unsavedChanges = this.$refs.proofWindow.some(
          (pw) => pw.notebook && pw.notebook.unsavedChanges
      );
      if (unsavedChanges) {
        const closeAnyway = window.confirm('Some tabs contain unsaved ' +
            'changes, are you sure you want to close them?');
        if (!closeAnyway) {
          return;
        }
      }
      window.location.href = 'index.html';
    },

    /**
     * Adds the specified file to the list of recent files
     *
     * @param {string} location  The path to the file
     */
    addToRecentFileList: function(location) {
      this.recents.addFileListEntry(location);
    },
    toggleDebug: function() {
      this.debug = !this.debug;
    },

    /**
     * Calls the method with the provided name on the current proof window,
     * if there are arguments provided these are passed into this method
     *
     * @param {object} event  An object with an attribute "detail" which
     *   contains either the name of the method to be called, or an object
     *   with attributes "method" and "detail", containing the method name
     *   and the arguments respectively.
     */
    doOnActiveProofWindow: function(event) {
      this.currentProofWindow.forwardEvent(event);
    },

    /**
     * Calls the method with the provided name of this class
     * if there are arguments provided these are passed into this method
     *
     * @param {object} event  An object with an attribute "detail" which
     *   contains either the name of the method to be called, or an object
     *   with attributes "method" and "detail", containing the method name
     *   and the arguments respectively.
     */
    doOnEdit: function(event) {
      if (typeof event === 'object') {
        this[event.method](event.detail);
      } else {
        this[event]();
      }
    },

    refreshExecGutters: function() {
      for (const proofWindow of this.$refs.proofWindow) {
        proofWindow.$refs.editWindow.alignGutter(false);
      }
    },

    toggleCommon: function(number) {
      // number is a magical constant from store.js
      // corresponding to one of the side menus
      this.$store.commit('toggleSideWindow', number);
    },
    openAboutPage: function() {
      this.$bvModal.show('about-modal');
    },
  },
  created: function() {
    if (process.env.NODE_ENV !== 'test' &&
        process.env.NODE_ENV !== 'coverage') {
      // cant import this in tests, :/ very ugly solution
      const ipcRenderer = require('electron').ipcRenderer;
      ipcRenderer.on('closing-application', () => {
        for (const tab of this.$refs.proofWindow) {
          if (tab.notebook && tab.notebook.unsavedChanges) {
            const {dialog} = require('electron').remote;

            const dialogOptions = {type: 'warning', title: 'Waterproof',
              buttons: ['Yes', 'Cancel'],
              message: 'There are unsaved changes. ' +
              'Are you sure you want to close Waterproof?',
            };

            // index of button
            const result = dialog.showMessageBox(dialogOptions);
            if (result === 1) {
              return;
            }
            break;
          }
        }

        const sendClose = () => {
          ipcRenderer.send('confirmClosing');
        };

        setTimeout(sendClose, 1000);

        this.socket.stopAll(sendClose);
      });

      this.socket = new TCPManager;
    }
  },
  mounted: function() {
    this.mainBus.$on('on-edit', this.doOnEdit);
    this.mainBus.$on('on-proof-window', this.doOnActiveProofWindow);
    this.mainBus.$on('goto-homescreen', this.homeScreen);

    window.onresize = this.refreshExecGutters;

    const url = window.location.href;

    if (url.includes('?')) {
      const parameter = url.split('?').pop();
      const filePath = decodeURIComponent(parameter);
      this.tabs.push({
        id: this.tabIdCounter++,
        fileURI: filePath,
      });
      this.addToRecentFileList(filePath);
    } else {
      this.tabs.push({
        id: this.tabIdCounter++,
        fileURI: null,
      });
    }
  },
  beforeDestroy() {
    this.socket.stopAll(() => {}, false);
  },
};
</script>

<style lang="scss">
  @import '../assets/sass/pages/edit';

  .about-content {
    font-size: 14px;
  }

</style>
