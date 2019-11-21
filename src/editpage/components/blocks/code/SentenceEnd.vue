<template>
    <span :class="['sentence-end-tag', 'sentence-end-' + index]"
          @click="executeTo" :data-special="special">
        <img v-if="special === 'done'" class="exec-inline-tick"
             alt="Done" src="../../../../assets/images/tick.svg">
        <img v-if="special === 'doing'" class="exec-inline-spinner"
             alt="Processing" src="../../../../assets/images/druppel.png">
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
  },
  methods: {
    executeTo() {
      if (!this.clickable) {
        return;
      }
      console.log('exec to', this.index);
    },
  },
};
</script>

<style lang="scss">
    .exec-inline-tick {
        float: left;
        height: 1em;
        width: 1em;
        align-self: center;
        vertical-align: text-top;
    }

    .exec-inline-spinner {
        float: left;
        height: 1em;
        width: 1em;
        align-self: center;
        vertical-align: text-top;
        animation: spin 4s linear infinite;
    }

    @keyframes spin {
        100% {
            transform: rotate(360deg);
        }
    }

    .sentence-end-tag:after {
        content: "";
        position: absolute;
        top: 0;
        left: 0;
        width: 1em;
        height: 1em;
        display: inline-block;
    }

    .sentence-end-tag[data-special=""]:hover:after {
        background-color: $color-primary;
        cursor: pointer;
        mask-type: alpha;
        mask-repeat: no-repeat;
        -webkit-mask-repeat: no-repeat;
        -webkit-mask-position: center center;
        -webkit-mask-size: 40px 15px;
        -webkit-mask-image: url("../../../../assets/images/arrowToCursor.svg");
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
