<template>
  <div>
    <div @click="toggleFold">
        <span v-if="!unfolded">►</span>
        <span v-else>▼</span>
        {{item.name}}
    </div>
    <div class="symbol-list" v-if="unfolded">
      <maths-symbol
        v-for="(symbol, index) in item.elements"
        v-bind:item="symbol" :event-bus="eventBus"
        v-bind:key="'symbol' + index" />
    </div>
  </div>
</template>

<script>
import MathsSymbol from './MathsSymbol.vue';

export default {
  name: 'SymbolCategory',
  props: ['item', 'eventBus'],
  components: {
    MathsSymbol,
  },
  data: function() {
    return {
      unfolded: true,
    };
  },
  methods: {
    toggleFold: function() {
      this.unfolded = !this.unfolded;
    },
  },
};
</script>

<style lang="scss">
  .symbol-list {
      display: flex;
      flex-flow: row wrap;
      justify-content: space-evenly;
      background-color: $color-gray-light;
      padding: 4px;
  }
</style>
