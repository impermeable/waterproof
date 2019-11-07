<template>
    <div class="loader-footer" :style="{'max-height': maxHeight}">
        {{loadState}}
    </div>
</template>

<script>
import {mapState} from 'vuex';

export default {
  name: 'Loader',
  computed: {
    ...mapState({
      loadState: (state) => state.libraries.message,
      done: (state) => state.libraries.done,
    }),
    maxHeight: function() {
      return this.done ? '0' : '45px';
    },
  },
  created() {
    this.$store.dispatch('loadSerapi');
  },
};
</script>

<style>
    .loader-footer {
        position: absolute;
        bottom: 0;
        color: red;
        width: 100%;
        background-color: purple;
        transition: max-height 0.5s;
        transition-delay: 0.5s;
        overflow: hidden;
        padding: 0 25px;
    }
</style>
