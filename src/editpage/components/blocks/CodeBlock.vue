<template>
  <div style="display: inline" >
      <p v-if="startWithBreak"></p>
      <span v-if="inline"
            @click="handleClick($event)"
            @contextmenu="handleRightClick($event)"
            :class="[{'selected-block': isSelected}, codeStyle]"
            tabindex="-1"
            v-html="formattedText" contenteditable="false">
      </span>
      <pre v-else
            @click="handleClick($event)"
            @contextmenu="handleRightClick($event)"
            :class="[{'selected-block': isSelected}, codeStyle]"
            tabindex="-1"
            v-html="formattedText" contenteditable="false">
      </pre>
      <div v-if="hasErrorBlock" class="exec-error">
          {{block.state.error.message}}
      </div>
      <p v-if="endWithBreak"></p>
  </div>
</template>

<script>
import WpBlock from './WpBlock';

export default {
  name: 'CodeBlock',
  mixins: [WpBlock],
  computed: {
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
    makeTick: function() {
      // The tick replaces the . at the end of a sentence, and also the
      // space after it if it exists (so not if the sentence ens in a \n)
      return `<span class="exec-span"><img class="exec-inline-tick" `
        + `src="${tick}"/></span>`;
    },
    makeSentenceEnd: function(index, type='') {
      let img = '';
      if (type === 'done') {
        img = `<img class="exec-inline-tick" src="${tick}"/>`;
      } else if (type === 'doing') {
        img = `<img class="exec-inline-spinner" src="${spinner}"/>`;
      }
      return `<span class="sentence-end-tag sentence-end-${index}">`
           + img
           + '</span>';
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
  },
};

const tick = require('../../../assets/images/tick.svg');
const spinner = require('../../../assets/images/druppel.png');
</script>


<style>
  pre.code-block {
    margin: 5px 0;
    white-space: pre-wrap;
    word-break: break-word;
    display: block;
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
    width: 0em;
    align-self: center;
    text-align: center;
    background-position-x: center;
    background-position-y: center;
    display: inline-block;
  }

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

  .exec-error {
    color: white;
    background: red;
    border: 1px solid red;
  }

  .exec-inline-error {
    text-decoration: underline red wavy;
  }

  /*.sentence-end-tag:before {*/
  /*    content: "";*/
  /*    float: left;*/
  /*    position: relative;*/
  /*    top: 5px;*/
  /*    left: -10px;*/
  /*    min-width: 5px;*/
  /*    min-height: 5px;*/
  /*    background-color: red;*/
  /*    display: inline-block;*/
  /*}*/

  .sentence-end-tag {
      height: 1em;
      width: 0em;
      align-self: center;
      text-align: center;
      background-position-x: center;
      background-position-y: center;
      display: inline-block;
  }
</style>
