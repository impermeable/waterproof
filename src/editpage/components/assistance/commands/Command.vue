<template>
    <div class="assistance-item">
      <hr v-if="hasPrevious">
      <div class="content-and-copy">
        <div>
          <span class="title" @click="toggleFold">
            {{ item.name }}
          </span>
          <br>
          <span @click="toggleFold">
            <span v-if="!unfolded">►</span>
            <span v-else>▼</span>
            {{ item.description }}
          </span>
          <!-- Needs to be on one line to make it show up right -->
          <div v-if="unfolded"
                class="code-block command-example"
              >{{ item.example }}<div
                class="button-execute"
                @click="execute()">►</div>
          </div>
        </div>
        <div class="insert-buttons">
          <img src="../../../../assets/images/copy.svg"
            class="button-insert"
            @click="copyToClipboard(item.name)"/>
        </div>
      </div>
    </div>
</template>


<script>
import AssistanceItem from '../AssistanceItem.vue';

export default {
  name: 'Command',
  mixins: [AssistanceItem],
  data: function() {
    return {
      unfolded: false,
    };
  },
  methods: {
    toggleFold: function() {
      this.unfolded = !this.unfolded;
    },
    execute: function() {
      this.eventBus.$emit('coqSearch', {
        query: this.item.example,
        fromExample: this.item.name,
      });
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
