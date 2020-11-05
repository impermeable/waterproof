<template>
    <div class="assistance-item" v-if="!isAdvanced || showAdvanced">
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
          <div v-if="unfolded" class="code-block">{{ item.example }}</div>
        </div>
        <div class="insert-buttons">
          <img src="../../../../assets/images/copy.svg"
            class="button-insert"
            @click="copyToClipboard(item.name)"/>
          <img src="../../../../assets/images/insertAtCursor.svg"
            class="button-insert"
            @click="insertAtCursor(item.name)"/>
        </div>
      </div>
    </div>
</template>


<script>
import AssistanceItem from '../AssistanceItem.vue';

export default {
  name: 'Tactic',
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
  },
  computed: {
    isAdvanced() {
      return this.item.hasOwnProperty('advanced') && this.item.advanced;
    },
  },
};
</script>

<style lang="scss">
</style>
