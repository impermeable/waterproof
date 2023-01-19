<script>
const md = require('markdown-it')();
const mk = require('@iktakahiro/markdown-it-katex');
md.use(mk);
const regExp = /<p>(.*)<\/p>/si;

export default {
  props: {
    block: Object,
    index: Number,
    exercise: Boolean,
    eventBus: {$on: Function, $emit: Function},
    sentences: Array,
    executedIndex: Number,
    runningIndex: Number,
  },
  data: function() {
    return {
      selected: false,
    };
  },
  methods: {
    handleClick: function(event) {
      const isBlockSelection =
          process.platform === 'darwin' ? event.metaKey : event.ctrlKey;
      if (this.isEditable) {
        if (event.shiftKey) {
          this.eventBus.$emit('select-range', this.block);
        } else if (isBlockSelection) {
          this.eventBus.$emit('select-single', this.block);
        } else {
          if (this.block.state.foldStatus.startFold) {
            this.eventBus.$emit('unfold', this.block);
          }
          if (this.block.type !== 'input') {
            let cursorIndex = -1;

            const sel = window.getSelection();
            if (!sel.isCollapsed) {
              this.eventBus.$emit('set-focus', this.index, {cursorIndex});
              return;
            }

            try {
              let node = sel.focusNode;
              const dataTextIndexAttribute = 'data-text-index';

              if (node.nodeType === Node.TEXT_NODE) {
                const parent = node.parentNode;
                const sibling = node.previousElementSibling;

                // Prefer parent element, then previous sibling
                // and otherwise go up the tree.
                if (parent.getAttribute(dataTextIndexAttribute) != null) {
                  node = parent;
                } else if (sibling != null && sibling.getAttribute(
                    dataTextIndexAttribute) != null) {
                  node = sibling;
                } else {
                  node = parent;
                }
              }

              while (node != null
                && node.getAttribute(dataTextIndexAttribute) == null) {
                const parent = node.parentNode;
                if (parent.getAttribute('data-block-search-stop') != null) {
                  node = null;
                  break;
                }
                node = parent;
              }

              if (node != null) {
                const textIndex =
                    node.getAttribute(dataTextIndexAttribute) || '';
                const number = parseInt(textIndex);
                if (textIndex !== '' && !Number.isNaN(number)) {
                  cursorIndex = parseInt(textIndex) + sel.anchorOffset;
                }
              }
            } catch (e) {
              console.log('went wrong in text index look up', e);
            }

            this.eventBus.$emit('set-focus', this.index, {cursorIndex});
          }
        }
      }
    },
    handleRightClick: function(event) {
      if (this.isEditable) {
        this.$parent.$refs.menu.open(event, this.block);
      }
    },
    render: function(text) {
      // Replace coqdoc-style headers (*) with markdown headers (#)
      let converted = text.replace(/^[ ]*([*]+) /gm, (match, p1) => {
        return '#'.repeat(p1.length) + ' ';
      });
      // Replace coqdoc-style lists (-) with markdown lists (*)
      converted = converted.replace(/^([ ]*)- /gm, '$1* ');
      return md.render(converted);
    },
    renderToSpan: function(text) {
      let htmlString = this.render(text);
      // htmlString = htmlString.replace(/\n/g, '<br>');
      htmlString = htmlString.replace(regExp, '<span>$1</span>');
      return htmlString;
    },
  },
  computed: {
    startWithBreak: function() {
      return this.block.text.startsWith('\n');
    },
    endWithBreak: function() {
      return this.block.text.endsWith('\n');
    },
    isSelected: function() {
      return this.block.state.isSelected;
    },
    isEditable: function() {
      return !this.exercise || this.block.state.inInputField;
    },
  },
};
</script>

<style lang="scss">
@import '../../../assets/sass/_colors.scss';
  .selected-block {
    @include theme(background-color, color-primary-ultra-light,
        null, !important);
    @include theme(background-color, color-black);
  }

  .selected-block *:not(.katex) {
    @include theme(background-color, color-primary-ultra-light,
        null, !important);
    @include theme(color, color-black, null, !important);
  }

  .selected-block .katex * {
    @include theme(background-color, color-transparent, null, !important);
  }

  .wap-block {
    display: inline;
    word-break: break-word;
  }
</style>
