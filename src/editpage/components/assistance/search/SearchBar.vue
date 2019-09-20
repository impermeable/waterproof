<template>
    <div class="search-bar">
        <img src="../../../../assets/images/commandButton.svg"
          class="tactic-button" @click="showCommands" />
        <img src="../../../../assets/images/symbolButton.svg"
          class="tactic-button" @click="showSymbols" />
        <img src="../../../../assets/images/tacticButton.svg"
          class="tactic-button" @click="showTactics" />
        <div class="search-container">
            <textarea class="input-field" id="search-query"
                      v-model="searchText"
                @keydown.enter.exact.prevent
                @keyup.enter="showResults()">
            </textarea>
            <input type="button" class="corner" @click="showResults" />
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
  },
};
</script>

<style scoped lang="scss">
  .search-bar {
    display: flex;
    align-items: center;
    margin-top: 40px;
  }

  .tactic-button {
    cursor: pointer;
    height: 25px;
    position: relative;
    margin-right: 8px;
  }

  .search-container {
    height: 45px;
    position: relative;

    .input-field {
      height: 40px;
      outline: 0;
      width: 350px;
      resize: none;
      border-radius: 20px;
      border: 1px #000 solid;
      padding: 5px 5px 5px 40px;
      margin-right: 10px;
    }

    .corner {
      position: absolute;
      top: 7px;
      left: 12px;
      height: 26px;
      width: 26px;
      border-radius: 10px;
      border: none;
      background: url("../../../../assets/images/looking_glass_grey.svg");
    }
  }
</style>
