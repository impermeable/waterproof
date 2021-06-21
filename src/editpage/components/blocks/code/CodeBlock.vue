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
                    v-html="part.text">
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
      let text = this.block.text.trimStart();
      const diff = this.block.text.length - text.length;
      console.log('diff', diff);
      text = text.trimEnd();

      // Determine where to insert error, tick, or both
      const sentences = this.localSentences.map((i) => {
        return {
          at: i.end - diff,
          what: 'sentence-end',
          ast: i.ast,
          start: i.start - diff};
      });
      // if (this.hasError) {
      //   splitAt.push({
      //     at: this.block.state.error.from,
      //     what: 'error-start',
      //   });
      //   splitAt.push({
      //     at: this.block.state.error.to,
      //     what: 'error-end',
      //   });
      // }

      if (sentences.length === 0) {
        return [
          {
            text: this.block.text.trim(),
          },
        ];
      }

      const parts = [];
      // sentences.sort((obj1, obj2) => obj1.at - obj2.at);
      // console.log(sentences); // TODO uncomment and deal with this next.
      let index = 0;
      // let inError = false;
      for (const obj of sentences) {
        // console.log(obj); // TODO uncomment and deal with this next.
        // console.log('AST', obj.ast);
        const newIndex = obj.at;
        // prefix
        parts.push({
          text: text.slice(index, obj.start),
        });
        index = obj.start;
        const sentenceText = text.slice(index, newIndex);
        parts.push({
          text: this.colorText(sentenceText, obj.ast),
        });
        // const h = Math.floor(Math.random() * 24) * 15;
        // parts.push({
        //   text: `<span style="color: hsl(${h}, 90%, 50%)">` +
        //       + '</span>',
        // });
        // parts.push({
        //   text: '.',
        // });
        index = obj.at;
        // if (obj.what === 'error-start') {
        //   inError = true;
        // } else if (obj.what === 'error-end') {
        //   inError = false;
        // } else if (obj.what === 'sentence-end') {
        // console.log(index);
        const realIndex = newIndex + this.block.state.textIndex;
        let type = '';
        if (realIndex === this.executedIndex) {
          type = 'done';
          // skip a character (the final .)
          index++;
        } else if (realIndex === this.runningIndex) {
          type = 'doing';
          // skip a character (the final .)
          index++;
        }

        parts.push({
          end: true,
          index: realIndex,
          special: type,
        });

        if (this.inline && index === text.length) {
          parts.push({
            text: ' ',
            special: true,
          });
        }
        // }
      }

      if (index < text.length) {
        parts.push({
          text: text.slice(index),
        });
      }

      return parts;
    },
    hasError: function() {
      return this.block.state.error !== null &&
        this.block.state.error !== undefined;
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
    localSentences() {
      const allSentences = [...Array(this.state.sentenceSize()).keys()]
          .map((i) => {
            return {
              ast: this.state.getFlatAST(i),
              end: this.state.endIndexOfSentence(i) -
                     this.block.state.textIndex,
              start: this.state.beginIndexOfSentence(i)-
                  this.block.state.textIndex,
            };
          })
          .filter(({end}) => end >= 0 && end <= this.block.text.length);
      // console.log(allSentences);
      return allSentences;
      // console.log(this.block);
      // return this.sentences.map((s) => s - this.block.state.textIndex)
      //     .filter((i) => i >= 0)
      //     .filter((i) => i <= this.block.text.length);
    },
  },
  methods: {
    colorText: function(text, ast) {
      // console.log('Coloring', text, 'with', ast);
      if (ast == null || ast.length === 0) {
        return this.escapeHtml(text);
      }

      let html = '';
      let index = 0;

      const part = (to) => {
        const val = this.escapeHtml(text.slice(index, to));
        index = to;
        return val;
      };

      const toHue = function(str) {
        let hash = 0;
        if (str.length === 0) return hash;
        for (let i = 0; i < str.length; i++) {
          hash = str.charCodeAt(i) + ((hash << 5) - hash);
          hash = hash & hash;
        }
        return 4 * (hash % 90) + hash % 4;
      };

      console.warn('COLORING!!!', ast.flatAst);
      for (const range of ast) {
        html += part(range.start);
        const pp = part(range.end);
        const h = toHue(range.type);
        html += `<span style="color: hsl(${h}, 60%, 50%)">${pp}</span>`;
      }
      html += `<span class="final-append">${part(text.length)}</span>`;

      return html;
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
