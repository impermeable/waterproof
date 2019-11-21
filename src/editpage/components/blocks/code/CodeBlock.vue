<template>
  <div style="display: inline" >
<!--      <p v-if="startWithBreak"></p>-->
      <inlineable :inline="inline" @click="handleClick($event)"
                  @contextmenu="handleRightClick($event)"
                  :class="[{'selected-block': isSelected}, codeStyle]"
                  tabindex="-1"
                  contenteditable="false">
          <template v-for="(part, index2) of parts">
              <span v-if="part.type === 'code'"
                    :key="'code-' + index + '-part-' + index2"
                    :class="{'exec-inline-error': part.error}"
                    v-html="codeToHtml(part.text)">
              </span>
              <SentenceEnd v-else-if="part.type === 'end'"
                           :key="'code-' + index + '-end-' + index2"
                           :index="part.index" :special="part.special"/>
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
    parts: function() {
      return [
        {
          type: 'code',
          text: 'Check plus',
        },
        {
          type: 'end',
          index: 15,
          special: 'done',
        },
        {
          type: 'code',
          text: '.\n',
        },
        {
          type: 'code',
          text: 'Check ',
        },
        {
          type: 'code',
          error: true,
          text: 'plus',
        },
        {
          type: 'end',
          index: 32,
          special: '',
        },
        {
          type: 'code',
          text: '.',
        },
      ];
    },
    formattedText: function() {
      const text = this.block.text.trim();

      // Determine where to insert error, tick, or both
      const splitAt = this.foundSentences.map((i) => {
        return {at: i, what: 'sentence-end'};
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

      let newText = '';
      // Sort from last to first
      splitAt.sort((obj1, obj2) => obj1.at - obj2.at);
      let index = 0;
      for (const obj of splitAt) {
        const newIndex = obj.at;
        newText = newText + this.highlight(this.escapeHtml(
            text.slice(index, newIndex)
        ));
        index = newIndex;
        if (obj.what === 'error-start') {
          newText = newText + '<span class="exec-inline-error">';
        } else if (obj.what === 'error-end') {
          newText = newText + '</span>';
        } else if (obj.what === 'tick') {
          // Take the last '.' and replace it with the tick
          const insertAt = newText.lastIndexOf('.');
          newText = newText.slice(0, insertAt)
           + this.makeTick() + ' '
           + newText.slice(insertAt + 1);
        } else if (obj.what === 'sentence-end') {
          const realIndex = newIndex + this.block.state.textIndex;
          let type = '';
          if (realIndex === this.executedIndex) {
            type = 'done';
          } else if (realIndex === this.runningIndex) {
            type = 'doing';
          }

          const insertAt = newText.lastIndexOf('.');

          if (type === '') {
            newText = newText.slice(0, insertAt)
              + this.makeSentenceEnd(realIndex, type)
              + newText.slice(insertAt);
          } else {
            newText = newText.slice(0, insertAt)
              + this.makeSentenceEnd(realIndex, type) + ' '
              + newText.slice(insertAt + 1);
          }
        }
      }
      newText = newText + this.highlight(this.escapeHtml(text.slice(index)));
      return newText;
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
        'codeExecuted': this.block.state.done,
        'code-block': true,
        'code-block-not-selected': !this.isSelected,
        'wap-block': true,
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
    makeSentenceEnd: function(index, type='') {
      return `<span class="sentence-end-tag sentence-end-${index}"></span>`;
    },
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
  },
};

</script>


<style lang="scss">
  pre.code-block {
    margin: 5px 0;
    display: block;
    white-space: pre-line;
    overflow: visible;
  }

  .code-block-not-selected {
    background: #f2f2f2;
  }

  .code-block {
    margin-right: 5px;
    font-family: monospace, monospace;
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
    color: white;
    background: red;
    border: 1px solid red;
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
