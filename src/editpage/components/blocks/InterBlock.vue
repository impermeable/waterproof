<template>
  <div v-if="isVisible"
      :class="[{'interblock': !wide}, {'start-interblock': wide},
          {'blinking': active && !wide}, {'start-blinking': active && wide}]"
      @click="$parent.setFocusedInterblock(index)">
    <span v-if="!wide">|</span>
    <span v-if="active"
    v-shortkey="{
                    Right: ['arrowright'],
                    Left: ['arrowleft'],
                    Up: ['arrowup'],
                    Down: ['arrowdown'],
                }"
    @shortkey="$parent.moveSelection">
    </span>
  </div>
</template>

<script>
export default {
  name: 'Interblock',
  props: {
    active: Boolean,
    wide: Boolean,
    exercise: Boolean,
    block: Object,
    index: Number,
  },
  computed: {
    isVisible: function() {
      // The top cursor is available iff it is not an exercise sheet
      if (!this.block) {
        return !this.exercise;
      }
      // Folded blocks have no cursor
      // but fold blocks themself might
      if (this.block.state.foldStatus.isFolded &&
          !this.block.state.foldStatus.startFold) {
        return false;
      }
      // All other blocks in a non-exercise sheet do
      if (!this.exercise) {
        return true;
      }
      // In exercise sheets, cursors only appear after the first input block
      if (this.block.type === 'input') {
        return this.block.start;
      }
      // and in the input fields themselves
      return this.block.state.inInputField;
    },
  },
};
</script>

<style lang="scss" scoped>
  .start-blinking {
    animation: 1s start-blink step-end infinite;
  }

  @keyframes start-blink {
    from, to {
      background-color: transparent;
    }
    50% {
      background-color: $color-primary-light;
    }
  }

  .start-interblock {
    width: 100%;
    height: 2px;
    padding: 2px 0;

    &:hover {
      background-color: $color-primary-light;
      cursor: pointer;
    }
  }

  .blinking {
    animation: 1s blink step-end infinite;
  }

  @keyframes blink {
    from, to {
      color: transparent;
    }
    50% {
      color: $color-primary;
    }
  }

  .interblock {
    margin-left: -4px;
    display: inline-block;
    color: transparent;
    user-select: none;

    &:hover {
      color: $color-primary;
      cursor: pointer;
    }
  }
</style>


