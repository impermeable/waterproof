<template>
  <div :class="['input-block', {'selected-block': isSelected},
       block.start ? 'input-start-block' : 'input-end-block']"
       @click="handleClick($event)" tabindex="-1"
       @contextmenu="handleRightClick($event)">
  </div>
</template>

<script>
import WpBlock from './WpBlock';

export default {
  name: 'InputBlock',
  mixins: [WpBlock],
};
</script>

<style lang="scss" scoped>
  .input-block {
    min-height: 1em;
  }

  .input-start-block {
    border: 3px solid $color-primary-light;
    border-bottom: 0;
    margin-bottom: 7px;
  }

  .input-end-block {
    border: 3px solid $color-primary-light;
    margin-top: 7px;
    border-top: 0;
  }
</style>
