<template>
  <div class="search-bar">
    <div v-bind:class="{ 'hide-assistance-buttons': isSearchOpen }"
         class="assistance-buttons" >
      <img src="../../../../assets/images/commandButton.svg"
        class="sidewindow-button" @click="showCommands" />
      <img src="../../../../assets/images/symbolButton.svg"
        class="sidewindow-button" @click="showSymbols" />
      <img src="../../../../assets/images/tacticButton.svg"
        class="sidewindow-button" @click="showTactics" />
    </div>
    <div v-bind:class="{ 'hide-assistance-buttons': !isSearchOpen }"
         class="search-container">
      <textarea class="input-field" id="search-query"
                v-model="searchText"
          @keydown.enter.exact.prevent
          @keyup.enter="showResults()">
      </textarea>
      <input type="button" class="corner" @click="showResults" />
    </div>
    <div class="toggle-search">
      <img v-if="!isSearchOpen" src="../../../../assets/images/looking_glass_grey.svg"
        class="sidewindow-button" @click="toggleSearch" />
      <img v-else src="../../../../assets/images/tooltipExpand.svg"
        class="sidewindow-button" @click="toggleSearch" />
    </div>
  </div>
</template>

<script>

export default {
  name: 'SearchBar',
  props: {
    eventBus: Object,
  },
  data: function() {
    return {
      searchText: '',
      isSearchOpen: false,
    };
  },
  methods: {
    showResults() {
      this.eventBus.$emit('on-proof-window', {
        event: 'coqSearch',
        payload: this.searchText,
      });
    },
    showTactics() {
      this.$store.commit('openSideWindow', 1);
    },
    showSymbols() {
      this.$store.commit('openSideWindow', 2);
    },
    showCommands() {
      this.$store.commit('openSideWindow', 3);
    },
    toggleSearch() {
      this.isSearchOpen = !this.isSearchOpen;
    },
  },
};
</script>

<style scoped lang="scss">
  .corner {
    position: absolute;
    top: 7px;
    left: 12px;
    height: 26px;
    width: 26px;
    border-radius: 10px;
    border: none;
    background: url("../../../../assets/images/looking_glass_grey.svg");

    @include respond-to(sm-lower) {
      height: 22px;
      width: 22px;
    }
  }
</style>
