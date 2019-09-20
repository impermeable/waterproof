import Vue from 'vue';
import Vuex from 'vuex';
const path = require('path');

import readFile from './io/readfile';

Vue.use(Vuex);

export default new Vuex.Store({
  state: {
    searchResults: [],
    searchResultsLemma: [],
    searchResultsDefinition: [],
    isSearching: false,
    sideWindowIndex: -1, // search - tactics - symbols - commands

    assistanceItems: [],
    configLoaded: false,
    sertopPath: '',
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
      state.sideWindowIndex = index;
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
      state.sertopPath = result['sertopPath'];
      state.configLoaded = true;
    },
  },
  actions: {
    readAssistanceItems: function({commit, state}) {
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
      });
      readFile(path.join(basePath, 'commands.json'), (result) => {
        commit('setAssistanceItems', {index: 2, result: result});
      });
    },
    readConfig: function({commit, state}) {
      return new Promise((resolve, reject) => {
        let basePath;
        if (process.env.NODE_ENV === 'production') {
          basePath = path.join(__dirname, '../../wrapper/configuration/');
        } else {
          basePath = './wrapper/configuration';
        }
        readFile(path.join(basePath, 'wpconfig.json'), (result) => {
          commit('setConfig', result);
          resolve();
        });
      });
    },
    getSertopPath: function({commit, dispatch, state}) {
      return new Promise((resolve, reject) => {
        if (state.configLoaded) {
          resolve(state.sertopPath);
        } else {
          dispatch('readConfig').then((result) => {
            resolve(state.sertopPath);
          }, (reject) => {
            console.err('could not read config file');
          } );
        }
      });
    },
  },
  getters: {},
});
