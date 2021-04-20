<script>
export default {
  name: 'CodeMirrorHandler',
  data: function() {
    return {
      eventBus: null,
    };
  },
  methods: {
    getCMOptions: function(type) {
      return {
        // codemirror options
        mode: type === 'code' ? 'text/x-coq' : 'text',
        tabSize: 2,
        matchBrackets: true,
        lineNumbers: true,
        lineWrapping: true,
        line: true,
        placeholder: 'Type your ' + type + ' here...',
        // gutters: ['exec-gutter'],
        extraKeys: {
          // Close editor with Esc, shift-enter or ctrl-enter
          // Except Esc unselects everything first
          'Esc': (function(cm) {
            if (cm.somethingSelected()) {
              cm.setCursor(cm.getCursor());
              return;
            }
            this.$refs.find.resetFind();
            this.blurSource();
          }).bind(this),
          'Ctrl-Enter': (function() {
            this.$refs.find.resetFind();
            this.blurSource();
          }).bind(this),
          // Standard codemirror keybinding to indent with spaces
          'Tab': function(cm) {
            if (cm.somethingSelected()) {
              cm.execCommand('indentMore');
            } else {
              const spaces = Array(cm.getOption('indentUnit') + 1).join(' ');
              cm.replaceSelection(spaces);
            }
          },
          'Ctrl-Z': false,
          'Ctrl-Y': false,
        },
      };
    },
    cursorMove: function(cm) {
      const fromCursor = cm.getCursor(true);
      const toCursor = cm.getCursor(false);
      this.cursorPos = {
        block: this.focusedElement,
        from: fromCursor,
        fromIndex: cm.indexFromPos(fromCursor),
        to: toCursor,
        toIndex: cm.indexFromPos(toCursor),
        selection: fromCursor.ch !== toCursor.ch ||
          fromCursor.line !== toCursor.line,
      };
      this.eventBus.$emit('setCursorPos', this.cursorPos);
    },

    /**
     * Scrolls to the word (in the currently opened codemirror
     * instance) defined by the position in coords
     * @param {Boolean} coords represents the coordinates of
     * the word that is to be scrolled to, with respect to the
     * top left corner of the codemirror instance the word is
     * marked in. The coords are represented as an object with
     * attributes top, bottom, left and right, representing the
     * corresponding sides of the word.
     */
    scrollToWord: function(coords) {
      let offset = coords.top;
      const height = document.querySelector(
          `#edit-window-${this.tabindex}`,
      ).clientHeight;
      offset -= height/2;
      const codemirrorInstance = document.querySelector(
          `#edit-window-${this.tabindex} #source-editor`,
      );
      if (codemirrorInstance) {
        const VueScrollTo = require('vue-scrollto');
        VueScrollTo.scrollTo(codemirrorInstance, 1, {
          container: this.$refs.domEl,
          easing: 'linear',
          offset: offset,
          x: false,
          y: true,
        });
      }
    },
  },
};
</script>

<style lang="scss">
@import "../../../assets/sass/_colors.scss";

.CodeMirror {
  @include theme(background-color, color-gray-light);
  @include theme(color, color-on-background);

  &-gutter {
    @include theme(background-color, color-gray-dark);
  }
}

</style>
