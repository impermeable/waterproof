<template>
  <div class="assistance-bar">
    <div class="query-area">
      <textarea rows="1" id="query-input"
        placeholder="Type your (search) query here..." v-model="searchQuery"
        @keydown.enter.exact.prevent
        @keyup.enter="query()" />
      <div :class="{'buttons-bottom': true, 'no-query': !hasQuery}">
        <assistance-button
          v-for="(button, index) in buttonsBottom"
          :name="button.name" :icon="button.icon" :key="'assistance' + index"
          :action="button.action"
          :title="hasQuery ? '' : `Enter query above to ${button.name}`"
        />
      </div>
    </div>
    <div class="button-area">
      <assistance-button
        v-for="(button, index) in buttonsRight"
        v-bind:name="button.name"
        v-bind:icon="button.icon"
        v-bind:action="button.action"
        v-bind:big="button.big"
        v-bind:key="'assistance' + index" />
    </div>
  </div>
</template>

<script>
import AssistanceButton from './AssistanceButton';

export default {
  name: 'AssistanceBar',
  components: {
    AssistanceButton,
  },
  props: {
    eventBus: Object,
  },
  computed: {
    hasQuery: function() {
      return this.searchQuery.trim() !== '';
    },
  },
  data: function() {
    return {
      buttonsBottom: [
        {
          name: 'Search',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.query();
          },
        },
        {
          name: 'Check',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.query('Check');
          },
        },
        {
          name: 'Print',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.query('Print');
          },
          big: true,
        },
      ],
      buttonsRight: [
        {
          name: 'Tactics',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.$store.commit('openSideWindow', 1);
          },
        },
        {
          name: 'Symbols',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.$store.commit('openSideWindow', 2);
          },
        },
        {
          name: 'Commands',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          action: () => {
            this.$store.commit('openSideWindow', 3);
          },
        },
      ],
      searchQuery: '',
    };
  },
  methods: {
    query(command) {
      if (!this.hasQuery) {
        return;
      }

      let query = this.searchQuery;
      if (command !== undefined) {
        query = command + ' ' + query + '.';
      }

      this.eventBus.$emit('coqSearch', query);
    },
  },
};
</script>

<style lang="scss">
  @import '../../../assets/sass/_colors.scss';

  .assistance-bar {
    width: 100%;
    border-top: 0;
    display: flex;
    flex-direction: row;

    .query-area {
      // border-right: 1px solid black;
      flex: 1 1 70%;
      display: flex;
      flex-direction: column;
      @include respond-to(sm) {
        flex-basis: 50%;
      }

      #query-input {
        @include theme(background-color, color-gray-light);
        @include theme(color, color-on-background);
        width: 100%;
        flex-basis: 50%;
        margin: 0;
        resize: none;
        font-size: 16px;
      }

      .buttons-bottom {
        display: flex;
        flex-basis: 50%;
        flex-flow: row wrap;
      }
    }

    .no-query {
      .assistance-button {
        @include theme(background-color, color-gray-dark);
        @include theme(color, color-gray-light);
        cursor: not-allowed;
      }
    }

    .button-area {
      display: flex;
      flex-flow: row wrap;
      flex-basis: 30%;
      @include respond-to(sm) {
        flex-basis: 50%;
      }
      @include respond-to(xs) {
        display: none;
      }
    }
  }
</style>
