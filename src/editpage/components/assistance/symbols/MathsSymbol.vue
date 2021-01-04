<template>
  <div class="symbol-button" @click="insertAtCursor(item.symbol)">
      {{item.symbol}}
  </div>
</template>

<script>
import AssistanceItem from '../AssistanceItem.vue';

export default {
  name: 'MathsSymbol',
  props: ['item'],
  mixins: [AssistanceItem],
};
</script>

<style lang="scss">
@import '/../../../../assets/sass/_colors.scss';
  .symbol-button {
    height: 40px;
    width: 40px;
    cursor: copy;
    text-align: center;
    font-family: monospace, monospace;
    font-size: larger;

    &:hover {
      @include theme(background-color, color-gray-dark);
      font-weight: bold;
    }
  }
</style>
