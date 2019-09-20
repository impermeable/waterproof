<template>
  <div style="display:inline" :class="{'selected-block': isSelected}">
    <p v-if="startWithBreak"></p>
    <span :class="['wap-block', 'text-block', {'edit-block': isEditable}]"
          @click="handleClick($event)" tabindex="-1"
          @contextmenu="handleRightClick($event)"
          v-html="formattedText">
    </span>
    <p v-if="endWithBreak"></p>
  </div>
</template>

<script>
import WpBlock from './WpBlock';

export default {
  name: 'TextBlock',
  mixins: [WpBlock],
  computed: {
    formattedText: function() {
      return this.renderToSpan(this.block.text);
    },
  },
}
;
</script>

<style scoped>
</style>
