<template>
  <span style="display: inline"
        :class="[{'selected-block': isSelected},'unfold-button']"
        @click="handleClick($event)" tabindex="-1"
        @contextmenu="handleRightClick($event)" >
    +
  </span>
</template>

<script>
import WpBlock from './WpBlock';

export default {
  name: 'FoldBlock',
  mixins: [WpBlock],
};
</script>

<style lang="scss">
  .unfold-button {
    cursor: pointer;
    border: 1px solid black;
  }
</style>
