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
@import '../../../assets/sass/_colors.scss';
  .input-block {
    min-height: 1em;
  }

  .input-start-block {
    @include theme(border, color-primary-light, 3px solid);
    /* We use important here since theme sets the border directly in a higher
       priority style set (Same for below) */
    border-bottom-width: 0 !important;
    margin-bottom: 7px;
  }

  .input-end-block {
    @include theme(border, color-primary-light, 3px solid);
    margin-top: 7px;
    border-top-width: 0 !important;
  }
</style>
