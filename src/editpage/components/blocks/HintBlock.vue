<template>
  <div :class="[{'non-edit': exercise}, 'hint-base',
        {'selected-block': isSelected}]"
        @click="onClick($event)"
        @contextmenu="handleRightClick($event)">
    <div class="wap-block">
      <div v-if="showTitle" class="hint-block">
        <span tabindex="-1" v-html="formattedTitle">
        </span>
        <div class="hint-image-holder">
          <img alt="hint closed" class="hint-image"
               src="../../../assets/images/bulbOffWhite.svg">
        </div>
      </div>
      <hr v-if="showTitle && showText">
      <div v-if="showText" class="hint-block">
        <span tabindex="-1" v-html="formattedText">
        </span>
        <div class="hint-image-holder">
          <img alt="hint opened" class="hint-image"
               src="../../../assets/images/bulbOnWhite.svg">
        </div>
      </div>
    </div>
    <span v-if="!exercise && separatorLocation < 0"
          class="hint-error" @click="fixError">
      <strong>Warning</strong> no hint tag found, click to fix.
    </span>
  </div>
</template>

<script>
/*
   * {
   *  type: 'hint',
   *  title: 'Shown on unopened hint',
   *  text: 'Maybe you could use Proof.',
   * }
   */
import WpBlock from './WpBlock';
const HINT_SEPARATOR = '<hint>';
const DEFAULT_TITLE = 'Click to open hint';

export default {
  name: 'HintBlock',
  mixins: [WpBlock],
  data: function() {
    return {
      opened: false,
    };
  },
  computed: {
    separatorLocation: function() {
      return this.block.text.indexOf(HINT_SEPARATOR);
    },
    header: function() {
      return this.block.text.substr(0, this.separatorLocation);
    },
    body: function() {
      if (this.separatorLocation >= 0) {
        return this.block.text.substring(
            this.separatorLocation + HINT_SEPARATOR.length);
      } else {
        return this.block.text;
      }
    },
    formattedText: function() {
      return this.renderToSpan(this.body);
    },
    formattedTitle: function() {
      if (this.exercise && this.separatorLocation < 0) {
        return DEFAULT_TITLE;
      }
      return this.renderToSpan(this.header);
    },
    showTitle: function() {
      return !this.exercise || !this.opened;
    },
    showText: function() {
      return !this.exercise || this.opened;
    },
  },
  methods: {
    onClick: function(event) {
      if (this.exercise) {
        this.opened = !this.opened;
      } else {
        this.handleClick(event);
      }
    },
    fixError: function() {
      this.block.text = DEFAULT_TITLE + '\n'
        + HINT_SEPARATOR + '\n'
        + this.block.text;
    },
  },
};
</script>

<style lang="scss" scoped>
  .hint-base {
    position: relative;
    min-height: 1em;
    padding: 3px;
    margin-top: 0.5em;
    margin-bottom: 0.5em;

    background: $color-on-primary;
    border: 5px solid $color-primary;
  }

  .hint-block {
    position: relative;
    min-height: 1.1em;
    padding-right: 2em;
    margin: 4px 2px;
  }

  .hint-image {
    display: block;
    margin: auto;
    height: 1em;
  }

  .hint-image-holder {
    background: $color-primary-light;
    position: absolute;
    right: 0;
    top: 0;
    padding-top: 0.25em;
    min-height: 1.5em;
  }

  .hint-error {
    color: $color-on-primary;
    background: red;
    padding: 5px 5px 5px 5px;
    position: center;

    &:hover {
      cursor: pointer;
    }
  }

  .non-edit {
    user-select: none;

    &:hover {
      cursor: pointer;
    }
  }
</style>
