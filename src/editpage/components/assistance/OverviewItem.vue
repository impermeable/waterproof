<template>
    <div class="overview-item">
      <hr v-if="hasPrevious">
      <div class="content-and-copy">
        <div>
          <strong v-if="item.depth == 1"
              class="title" @click="visit">
            {{ item.title }}
          </strong>
          <span v-if="item.depth >= 1"
              class="title" @click="visit">
            {{ item.title }}
          </span>
          <!-- Needs to be on one line to make it show up right -->
        </div>
      </div>
    </div>
</template>


<script>
import AssistanceItem from './AssistanceItem.vue';

export default {
  name: 'Overview',
  mixins: [AssistanceItem],
  data: function() {
    return {};
  },
  methods: {
    visit() {
      this.eventBus.$emit('set-focus', this.item.index);
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
