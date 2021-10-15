<template>
  <div style="display: inline" @click="handleClick($event)">
      <p v-if="startWithBreak"></p>
      <inlineable :inline="inline"
                  @contextmenu="handleRightClick($event)"
                  :class="[{'selected-block': isSelected}, codeStyle]"
                  tabindex="-1"
                  contenteditable="false">
          <template v-for="(part, index2) of formattedText">
              <SentenceEnd v-if="part.end"
                           :key="'code-' + index + '-end-' + index2"
                           :index="part.index" :special="part.special"
                            @execTo="executeTo"/>
              <span v-else
                    :key="'code-' + index + '-part-' + index2"
                    :class="{'exec-inline-error': part.error}"
                    v-html="codeToHtml(part.text)">
              </span>
          </template>
      </inlineable>
      <div v-if="hasErrorBlock" class="exec-error">
          {{block.state.error.message}}
      </div>
      <p v-if="endWithBreak"></p>
  </div>
</template>

<script>
import WpBlock from '../WpBlock';
import Inlineable from './Inlineable';
import SentenceEnd from './SentenceEnd';

export default {
  name: 'CodeBlock',
  components: {SentenceEnd, Inlineable},
  mixins: [WpBlock],
  computed: {
    formattedText: function() {
      const whitespaceLength = this.block.text.length
          - this.block.text.trimStart().length;
      const text = this.block.text.trimEnd();

      // Determine where to insert error, tick, or both
      const splitAt = this.foundSentences.map((i) => {
        return {at: i - 1, what: 'sentence-end'};
      });
      if (this.hasError) {
        splitAt.push({
          at: this.block.state.error.from,
          what: 'error-start',
        });
        splitAt.push({
          at: this.block.state.error.to,
          what: 'error-end',
        });
      }

      const parts = [];
      // Sort from last to first
      splitAt.sort((obj1, obj2) => obj1.at - obj2.at);
      let index = whitespaceLength; // Instead of starting at 0.
      let inError = false;
      for (const obj of splitAt) {
        const newIndex = obj.at;
        if (newIndex > index) {
          parts.push({
            text: text.slice(index, newIndex),
            error: inError,
          });
        }
        index = newIndex;
        if (obj.what === 'error-start') {
          inError = true;
        } else if (obj.what === 'error-end') {
          inError = false;
        } else if (obj.what === 'sentence-end') {
          const realIndex = newIndex + this.block.state.textIndex + 1;
          let type = '';
          if (realIndex === this.executedIndex) {
            type = 'done';
          } else if (realIndex === this.runningIndex) {
            type = 'doing';
          }

          parts.push({
            end: true,
            index: realIndex,
            special: type,
          });

          if (this.inline && index === text.length) {
            parts.push({
              text: ' ',
            });
          }
        }
      }

      if (index < text.length) {
        parts.push({
          text: text.slice(index),
        });
      }

      return parts;
    },
    hasError: function() {
      return this.block.state.error !== null
        && this.block.state.error !== undefined;
    },
    hasErrorBlock: function() {
      return this.hasError && this.block.state.error.message;
    },
    inline: function() {
      return !this.block.text.trim().includes('\n');
    },
    codeStyle: function() {
      return {
        'code-block wap-block': true,
        'codeExecuted': this.block.state.done,
        'code-block-not-selected': !this.isSelected,
        'edit-block': this.isEditable,
      };
    },
    foundSentences() {
      return this.sentences.map((s) => s - this.block.state.textIndex)
          .filter((i) => i >= 0)
          .filter((i) => i <= this.block.text.length);
    },
  },
  methods: {
    highlight: function(text) {
      return text
          .replace(/\bLemma\b/g, '<span style="color:#2B39A7">Lemma</span>')
          .replace(/\bProof\b/g, '<span style="color:#2B39A7">Proof</span>')
          .replace(/\bQed\b/g, '<span style="color:#2B39A7">Qed</span>')
          .replace(/\bintro(s?)\b/g,
              '<span style="color:#22aa3f">intro$1</span>')
          .replace(/\bforall\b/g, '<span style="color:#bd4ebb">forall</span>');
    },
    escapeHtml: function(unsafe) {
      return unsafe
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;')
          .replace(/"/g, '&quot;')
          .replace(/'/g, '&#039;');
    },
    codeToHtml: function(code) {
      return this.highlight(this.escapeHtml(code));
    },
    executeTo(index) {
      this.eventBus.$emit('coqTo', index);
    },
  },
};

</script>


<style lang="scss">
  @import "../../../../assets/sass/_colors.scss";

  pre.code-block {
    margin: 5px 0;
    display: block;
    overflow: visible;

  }

  pre.code-block > span:first-child {
    margin-left: -2.4em;
  }

  .code-block-not-selected {
    @include theme(background-color, color-gray-light);
    @include theme(color, color-on-background);
  }

  .code-block {
    margin-right: 5px;
    @include theme(font-family, font-stack-code);
    white-space: pre-wrap;
    word-break: break-word;
  }

  .exec-span {
    content: "";
    font-family: monospace;
    height: 1em;
    width: 0;
    align-self: center;
    text-align: center;
    background-position-x: center;
    background-position-y: center;
    display: inline-block;
  }

  .exec-error {
    @include theme(color, color-error-text);
    @include theme(background-color, color-error);
    @include theme(border, color-error, 3px solid);
  }

  .exec-inline-error {
    position: relative;
    text-decoration: underline red dotted;
  }

  .exec-inline-error:after {
    position: absolute;
      width: 1em;
      height: 200%;
      content: ".";
      text-indent: -100em;
      margin-left: -1em;
  }
</style>
