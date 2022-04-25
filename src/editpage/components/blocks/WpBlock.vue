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
            this.eventBus.$emit('set-focus', this.index);
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
      // Remove coq-comment start & end
      converted = converted.replace(/\(\*/g, '(💧');
      converted = converted.replace(/\*\)/g, '💧)');
      // Translate code
      converted = converted.replace(/\[\[/g, '```');
      converted = converted.replace(/\]\]/g, '```');
      converted = converted.replace(/\[/g, '`');
      converted = converted.replace(/\]/g, '`');
      // Translate bold to md
      converted = converted.replace(/#<\/?strong>#/g, '**');
      // Translate italics to md
      converted = converted.replace(/[\s]_/g, ' *');
      converted = converted.replace(/_[\s.,!?]/g, '* ');

      converted = md.render(converted);
      return converted;
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
