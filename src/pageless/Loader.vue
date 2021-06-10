<template>
    <div class="loader-footer"
         :style="{'max-height': maxHeight}">
        <div :class="{'inner-load': true, 'failed-load': failed}">
            <scale-loader :loading="!done" :color="'white'"
                          :height="'15px'" class="scale-loader-lib">
            </scale-loader>
            <template v-if="failed">
              Serapi failed:
            </template>
            {{loadState}}
        </div>
    </div>
</template>

<script>
import {mapState} from 'vuex';
import ScaleLoader from 'vue-spinner/src/ScaleLoader';

export default {
  name: 'Loader',
  components: {
    ScaleLoader,
  },
  computed: {
    ...mapState({
      loadState: (state) => state.libraries.message,
      done: (state) => state.libraries.done,
      failed: (state) => state.libraries.fail,
    }),
    maxHeight: function() {
      return (this.done && !this.failed) ? '0' : '55px';
    },
  },
  created() {
    this.$store.dispatch('loadSerapi');
  },
};
</script>

<style lang="scss">
@import '../assets/sass/_colors.scss';
    .loader-footer {
        position: absolute;
        bottom: 0;
        left: 5%;
        @include theme(color, color-on-primary);
        width: 95%;
        @include theme(background-color, color-primary);
        transition: max-height 0.5s;
        transition-delay: 0.5s;
        overflow: hidden;
    }

    .inner-load {
        @include theme(border, color-primary-dark, 5px solid);
        border-right: 0;
        padding: 0 25px;
    }

    .scale-loader-lib {
        height: 20px;
        margin-top: 5px;
        margin-right: 1em;
        display: inline;
    }

    .failed-load {
       background-color: $color-error;
    }
</style>
