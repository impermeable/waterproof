<template>
    <span :class="['sentence-end-tag', 'sentence-end-' + index]"
          :data-special="special" @click.stop="executeTo" :title="hoverText">
        <img v-if="special === 'done'" class="exec-inline-tick"
             alt="Done" src="../../../../assets/images/tick.svg">
        <img v-else-if="special === 'doing'" class="exec-inline-spinner"
             alt="Processing" src="../../../../assets/images/spinner.svg">
    </span>
</template>

<script>
export default {
  name: 'SentenceEnd',
  props: {
    index: Number,
    special: String,
  },
  computed: {
    clickable() {
      return this.special === '';
    },
    hoverText() {
      if (this.special === 'done') {
        return 'Executed up to here';
      } else if (this.special === 'doing') {
        return 'Currently executing...';
      } else {
        return 'Execute upto here';
      }
    },
  },
  methods: {
    executeTo() {
      if (!this.clickable) {
        return;
      }
      this.$emit('execTo', this.index);
    },
  },
};
</script>

<style lang="scss">
@import '../../../../assets/sass/_colors.scss';
    .exec-inline-tick {
        height: 1em;
        width: 1em;
        align-self: center;
        vertical-align: text-top;
    }

    .exec-inline-spinner {
        height: 1em;
        width: 1em;
        align-self: center;
        vertical-align: text-top;
        animation: spin 2s linear infinite;
    }

    @keyframes spin {
        100% {
            transform: rotate(360deg);
        }
    }

    .sentence-end-tag::after, .sentence-end-tag::before{
        content: "";
        position: absolute;
        top: 4px;
        left: 0;
        width: 1em;
        height: 1em;
        display: inline-block;
    }

    .sentence-end-tag[data-special=""]:hover::after {
        cursor: pointer;
        @include theme(background-color, color-primary);
        mask-type: alpha;
        mask-repeat: no-repeat;
        -webkit-mask-repeat: no-repeat;
        -webkit-mask-position: center center;
        -webkit-mask-size: 40px 15px;
        -webkit-mask-image: url("../../../../assets/images/arrowToCursor.svg");
    }

    .sentence-end-tag[data-special=""]:hover::before {
        @include theme(background-color, color-gray-light);
    }

    .sentence-end-tag {
        position: relative;
        height: 1em;
        width: 0;
        align-self: center;
        text-align: center;
        display: inline-block;
    }
</style>
