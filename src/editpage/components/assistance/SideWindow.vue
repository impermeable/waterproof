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
        <h3 @click="updateOverview">
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
      <img src="../../../assets/images/refresh_black.svg" class="closing-icon"
          @click="updateOverview"/>
    </div>
    <hr>
    <div :class="{'search-results': windowIndex === 0}">
      <template v-for="(item, index) in sortedItems">
        <component :is="component"
                   :item="item" :hasPrevious="index > 0"
                   :showAdvanced="showAdvanced"
                   :event-bus="eventBus" :key="'assistanceItem' + index" />
      </template>

    </div>
    <template v-if="!showAdvanced && hasAdvanced">
      <div style="text-align: center">
        <hr>
        <a @click="showAdvanced = true" href="#">
          See more advanced {{ title.replace('Common', '') }}
        </a>
        <hr>
      </div>
    </template>
  </div>
</template>

<script>
import SearchResult from './search/SearchResult';
import Command from './commands/Command.vue';
import SymbolCategory from './symbols/SymbolCategory.vue';
import OverviewItem from './OverviewItem.vue';
import Tactic from './tactics/Tactic.vue';
import PulseLoader from 'vue-spinner/src/PulseLoader.vue';
import orderBy from 'lodash.orderby';

export default {
  name: 'SideWindow',
  props: {
    eventBus: Object,
    overview: Array,
  },
  components: {
    SearchResult,
    Command,
    SymbolCategory,
    OverviewItem,
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
      } else if (this.windowIndex === 4) {
        return this.overview;
      } else {
        return this.$store.state.assistanceItems[this.windowIndex - 1];
      }
    },
    hasAdvanced() {
      if (this.items.length === 0) {
        return false;
      }
      for (const item of this.items) {
        if (item.hasOwnProperty('advanced') && item.advanced) {
          return true;
        }
      }
      return false;
    },
    sortedItems() {
      return orderBy(this.items, [(item) => item.advanced || false], ['dsc']);
    },
  },
  watch: {
    windowIndex: function(newValue) {
      this.showAdvanced = false;
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
        case 4:
          this.title = 'Overview';
          this.component = 'overview-item';
      }
    },
  },
  data: function() {
    return {
      title: '',
      component: '',
      isShowingLemmas: true,
      isShowingDefinitions: true,
      showAdvanced: false,
    };
  },
  methods: {
    closeWindow: function() {
      this.$store.commit('closeSideWindow');
    },
    updateOverview() {
      if (this.windowIndex === 4) {
        this.eventBus.$emit('updateOverview');
      }
    },
  },
  mounted: function() {
    this.$store.dispatch('readAssistanceItems');
  },
};
</script>

<style lang="scss">
  @import '../../../assets/sass/_colors.scss';

    .side-window {
        flex: 1 0 25%;
        min-width: 250px;
        @include theme(background-color, color-gray);

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

      @include respond-to(sm-lower) {
        padding: 0 4px 0 4px;
      }
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

      h3 {
        @include respond-to(sm-lower) {
          font-size: 25px;
          margin-bottom: 0;
        }
      }
      .closing-icon {
        width: 22px;
        height: 22px;
        margin: 9px 18px 6px 6px;
        cursor: pointer;

        @include respond-to(sm-lower) {
          width: 18px;
          height: 18px;
        }
      }

      .filterbox {
        border-radius: 8px;
        width: 16px;
        height: 16px;
      }

      .label {
        @include theme(background-color, color-primary);
      }

      .loader {
        display: inline;

        .v-pulse{
          @include theme(background-color, color-primary, null, !important);
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
      @include theme(background-color, color-gray);
      @include theme(border, color-primary, 1px solid);
      border-radius: 5px;
      position: absolute;
      height: 20px;
      width: 20px;
      top: 0;
      left: 0;
    }

    .checklabel:after {
      @include theme(border, color-gray, 2px solid);
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
      @include theme(background-color, color-primary);
      @include theme(border-color, color-primary);
    }

    .round input[type="checkbox"]:checked + label:after {
      opacity: 1;
    }
</style>
