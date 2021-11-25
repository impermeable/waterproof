const remote = require('electron').remote;
const path = require('path');

import readFile from '../io/readfile';
import {readConfiguration, updateConfiguration} from '../io/configurationio';
import createTexInputHints from '../codemirror/tex-input';

import libraries from './libraries';

export default {
  modules: {
    libraries,
  },
  state: {
    searchResults: [],
    searchResultsLemma: [],
    searchResultsDefinition: [],
    isSearching: false,
    sideWindowIndex: -1, // search - tactics - symbols - commands

    assistanceItems: [],
    configLoaded: false,

    settings: {
      zoom: 1.0,
      theme: 'light',
      goalStyle: 'all',
    },
  },
  mutations: {
    onSearchStarted: function(state) {
      state.searchResults = [];
      state.searchResultsLemma = [];
      state.searchResultsDefinition = [];
      state.sideWindowIndex = 0;
      state.isSearching = true;
    },
    onSearchEnded: function(state) {
      state.isSearching = false;
    },
    onSearchResult: function(state, result) {
      if (result.isLemma) {
        state.searchResultsLemma.push(result);
      } else {
        state.searchResultsDefinition.push(result);
      }
      state.searchResults.push(result);
    },
    openSideWindow: function(state, index) {
      if (state.sideWindowIndex === index) {
        state.sideWindowIndex = -1;
      } else {
        state.sideWindowIndex = index;
      }
    },
    closeSideWindow: function(state) {
      state.sideWindowIndex = -1;
    },
    toggleSideWindow: function(state, index) {
      if (state.sideWindowIndex === index) {
        state.sideWindowIndex = -1;
      } else {
        state.sideWindowIndex = index;
      }
    },
    setAssistanceItems: function(state, {index, result}) {
      state.assistanceItems[index] = result;
    },
    setConfig: function(state, result) {
      if (result.hasOwnProperty('theme')) {
        state.settings.theme = result['theme'];
      }

      // Conformance. Must be 'light' or 'dark'. Default is light
      if (state.settings.theme == null || state.settings.theme === '') {
        state.settings.theme = 'light';
      }
      document.documentElement.className = state.settings.theme;

      if (result.hasOwnProperty('zoom')) {
        state.settings.zoom = result['zoom'];
      }
      // Conformance. Assume here the number is not zero and in range.
      if (state.settings.zoom == null || state.settings.zoom == 0.0 ||
          typeof state.settings.zoom !== 'number') {
        state.settings.zoom = 1.0;
      }
      const wf = require('electron').webFrame;
      wf.setZoomFactor(state.settings.zoom);

      state.configLoaded = true;
    },
    setZoom: function(state, factor) {
      state.settings.zoom = factor;
      const wf = require('electron').webFrame;
      wf.setZoomFactor(factor);

      updateConfiguration(remote, state.settings);
    },
    setTheme: function(state, theme) {
      state.settings.theme = theme;
      document.documentElement.className = theme;
      updateConfiguration(remote, state.settings);
    },
    setGoalStyle: function(state, goalStyle) {
      state.settings.goalStyle = goalStyle;
    },
  },
  actions: {
    readAssistanceItems: function({commit, state}) {
      if (state.assistanceItems.length > 0) {
        // if already loaded skip
        return;
      }
      let basePath;
      if (process.env.NODE_ENV === 'production') {
        basePath = path.join(__dirname, '../../wrapper/assistance/');
      } else {
        basePath = './wrapper/assistance';
      }
      readFile(path.join(basePath, 'tactics.json'), (result) => {
        commit('setAssistanceItems', {index: 0, result: result});
      });
      readFile(path.join(basePath, 'symbols.json'), (result) => {
        commit('setAssistanceItems', {index: 1, result: result});

        // now the tex input is only loaded when symbols is loaded
        createTexInputHints(result);
      });
      readFile(path.join(basePath, 'commands.json'), (result) => {
        commit('setAssistanceItems', {index: 2, result: result});
      });
    },
    readConfig: function({commit, state}) {
      return new Promise((resolve, reject) => {
        if (state.configLoaded) {
          resolve();
          return;
        }
        readConfiguration(remote).then(
            (data) => {
              commit('setConfig', data);
              resolve();
            }).catch(
            (err) => {
              console.log(err);
              reject(err);
            });
      });
    },
  },
};
