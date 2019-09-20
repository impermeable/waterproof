<template>
    <div class="assistance-item">
      <div class="content-and-copy">
        <div>
          <span class="title">
            <span class="result-object" >{{ item.objectName }} </span>
            {{ item.name }}
          </span>
          <br>
          <div>
              {{ item.content }}
          </div>
        </div>
        <div class="insert-buttons">
          <img src="../../../../assets/images/copy.svg"
            class="button-insert"
            @click="copyToClipboard(copyName)"/>
          <img src="../../../../assets/images/insertAtCursor.svg"
            class="button-insert"
            @click="insertAtCursor(copyName)"/>
        </div>
      </div>
      <hr v-if="!isLast">
    </div>
</template>


<script>
import AssistanceItem from '../AssistanceItem.vue';

export default {
  name: 'SearchResult',
  mixins: [AssistanceItem],
  computed: {
    copyName: function() {
      return this.item.name.replace(/:/g, '');
    },
  },
};
</script>

<style lang="scss">
  .result-object {
    color: $color-primary;
  }
</style>
