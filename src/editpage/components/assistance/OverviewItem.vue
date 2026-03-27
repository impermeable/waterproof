<template>
    <div class="overview-item">
      <div class="content-and-copy">
        <div v-if="item.visible" :style="`margin-top: ${
          item.depth == 1 ? 15 : item.depth == 2 ? 5 : 0
          }px;`">
          <div :style="`margin-left: ${(item.depth-1) * 30}px;`">
            <span v-if="children.length > 0" @click="toggleFold">
              <span v-if="!item.unfolded">►</span>
              <span v-else>▼</span>
            </span>
            <span v-else>◉</span>
            <span class="title" @click="visit">
              {{ item.text }}
            </span>
          </div>
        </div>
      </div>
    </div>
</template>


<script>
import AssistanceItem from './AssistanceItem.vue';

export default {
  name: 'Overview',
  mixins: [AssistanceItem],
  methods: {
    toggleFold: function() {
      this.item.unfolded = !this.item.unfolded;
      for (const child of this.children) {
        child.visible = this.item.unfolded;
      }
    },
    visit() {
      this.eventBus.$emit('scrollToOffset', this.item.offset);
    },
  },
};
</script>

<style lang="scss">
  .command-example {
    display: flex;
    justify-content: space-between;

    .button-execute {
      cursor: pointer;
      height: 24px;
    }
  }
</style>
