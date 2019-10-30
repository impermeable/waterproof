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
      return md.render(text);
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
  .selected-block {
    background-color: $color-primary-ultra-light !important;
    color: black;
  }

  .selected-block *:not(.katex) {
    background-color: $color-primary-ultra-light !important;
    color: black !important;
  }

  .selected-block .katex * {
    background-color: transparent !important;
  }

  .wap-block {
    display: inline;
    word-break: break-word;
  }
</style>
