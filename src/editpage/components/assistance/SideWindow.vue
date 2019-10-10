<template>
  <div v-show="isVisible"
       :class="['side-window', {'common-list': this.windowIndex !== 0}]"
       id="results">
    <div class="title-block">
      <img src="../../../assets/images/closing_cross.svg"
        class="closing-icon"
        @click="closeWindow"
      />
      <div>
        <h3>
          {{title}}
          <pulse-loader class="loader" :loading="isSearching" :size="'10px'">
          </pulse-loader>
        </h3>
        <!--<div v-if="windowIndex === 0">
          <div class="round">
            <input type="checkbox" id="lemmabox"
                  v-model="isShowingLemmas" />
            <label for="lemmabox" class="checklabel"></label>
            <label for="lemmabox" class="checkLabelText">Lemma</label>
          </div>
          <div class="round">
            <input type="checkbox" id="definitionbox"
                  v-model="isShowingDefinitions" />
            <label for="definitionbox" class="checklabel"></label>
            <label for="definitionbox" class="checkLabelText">
              Definition
            </label>
          </div>
        </div>-->
      </div>
    </div>
    <hr>
    <div :class="{'search-results': windowIndex === 0}">
      <component :is="component"
        v-for="(item, index) in items"
        v-bind:item="item"
        v-bind:isLast="index === (items.length - 1)"
                :event-bus="eventBus"
        v-bind:key="'assistanceItem' + index" />
    </div>
  </div>
</template>

<script>
import SearchResult from './search/SearchResult';
import Command from './commands/Command.vue';
import SymbolCategory from './symbols/SymbolCategory.vue';
import Tactic from './tactics/Tactic.vue';
import PulseLoader from 'vue-spinner/src/PulseLoader.vue';

export default {
  name: 'SideWindow',
  props: {
    eventBus: Object,
  },
  components: {
    SearchResult,
    Command,
    SymbolCategory,
    Tactic,
    PulseLoader,
  },
  computed: {
    windowIndex: function() {
      return this.$store.state.sideWindowIndex;
    },
    searchResults: function() {
      if (this.isShowingLemmas && this.isShowingDefinitions) {
        return this.$store.state.searchResults;
      }
      if (this.isShowingLemmas) {
        return this.$store.state.searchResultsLemma;
      }
      if (this.isShowingDefinitions) {
        return this.$store.state.searchResultsDefinition;
      }
    },
    isVisible: function() {
      return this.$store.state.sideWindowIndex !== -1;
    },
    isSearching: function() {
      return this.$store.state.isSearching;
    },
    items: function() {
      if (this.windowIndex === -1) {
        return [];
      } else if (this.windowIndex === 0) {
        return this.searchResults;
      } else {
        return this.$store.state.assistanceItems[this.windowIndex - 1];
      }
    },
  },
  watch: {
    windowIndex: function(newValue) {
      switch (newValue) {
        case 0:
          this.title = 'Search Results';
          this.component = 'search-result';
          break;
        case 1:
          this.title = 'Common Tactics';
          this.component = 'tactic';
          break;
        case 2:
          this.title = 'Mathematical Symbols';
          this.component = 'symbol-category';
          break;
        case 3:
          this.title = 'Commands';
          this.component = 'command';
          break;
      }
    },
  },
  data: function() {
    return {
      title: '',
      component: '',
      isShowingLemmas: true,
      isShowingDefinitions: true,
    };
  },
  methods: {
    closeWindow: function() {
      this.$store.commit('closeSideWindow');
    },
  },
  mounted: function() {
    this.$store.dispatch('readAssistanceItems');
  },
};
</script>

<style lang="scss">
    .side-window {
        flex: 1 0 25%;
        min-width: 250px;
        background-color: $color-gray;

        display: flex;
        flex-direction: column;
        justify-content: flex-start;
        overflow-x: hidden;

        .navigation {
          display: flex;
          width: 100%;
          justify-content: space-between;
          flex-direction: row;
        }
    }

    .common-list {
      padding: 0 8px 0 8px;
    }

    .search-results {
      display: flex;
      padding: 0 8px 0 8px;
      flex-direction: column;
      justify-content: flex-start;
      overflow-y: scroll;
        /* TODO: use a proper solution so the scrollbar
            does not show up in the first place */
      overflow-x: hidden;
    }

    .title-block {
      display: flex;

      .closing-icon {
        width: 22px;
        height: 22px;
        margin: 9px 18px 6px 6px;
        cursor: pointer;
      }

      .filterbox {
        border-radius: 8px;
        width: 16px;
        height: 16px;
      }

      .label {
        background-color: blue;
      }

      .loader {
        display: inline;

        .v-pulse{
          background-color: $color-primary !important;
        }
      }
    }

    .round {
      position: relative;
      display: inline;
      margin-right: 16px;
    }

    .round label {
      cursor: pointer;
    }

    .checklabel {
      background-color: $color-gray;
      border: 1px solid $color-primary;
      border-radius: 5px;
      position: absolute;
      height: 20px;
      width: 20px;
      top: 0;
      left: 0;
    }

    .checklabel:after {
      border: 2px solid $color-gray;
      border-top: none;
      border-right: none;
      content: "";
      height: 7px;
      width: 14px;
      top: 4px;
      left: 2px;
      opacity: 0;
      position: absolute;
      transform: rotate(-45deg);
    }

    .checkLabelText {
      margin-left: 5px;
    }

    .round input[type="checkbox"] {
      visibility: hidden;
      margin-right: 4px;
    }

    .round input[type="checkbox"]:checked + label {
      background-color: $color-primary;
      border-color: $color-primary;
    }

    .round input[type="checkbox"]:checked + label:after {
      opacity: 1;
    }
</style>
