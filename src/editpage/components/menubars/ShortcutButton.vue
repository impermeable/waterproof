<script>
export default {
  props: {
    buttonInfo: Object,
    shortKeys: Object,
    eventBus: Object,
  },
  methods: {
    /**
     * Sends an event containing the method that needs to be called
     * to the Edit instance
     */
    sendEvent: function() {
      if (this.buttonInfo.disabled) {
        return;
      }

      // TODO dont do this with this if
      if (this.buttonInfo.eventType === 'on-proof-window') {
        this.eventBus.$emit(this.buttonInfo.eventType, {
          event: this.buttonInfo.event,
        });
      } else {
        this.eventBus.$emit(this.buttonInfo.eventType,
            this.buttonInfo.event);
      }
    },
  },
  computed: {
    shortcut: function() {
      return this.shortKeys.shortKeys[this.buttonInfo.shortkeyTag];
    },
    titleText: function() {
      if (Array.isArray(this.shortcut)) {
        return `${this.buttonInfo.text} (${this.formattedShortcut})`;
      } else {
        return this.buttonInfo.text;
      }
    },
    formattedShortcut: function() {
      if (Array.isArray(this.shortcut)) {
        return this.shortcut.map((s) => {
          if (s === 'meta') {
            return '⌘';
          } else if (s === 'arrowup') {
            return '↑';
          } else if (s === 'arrowright') {
            return '→';
          } else if (s === 'arrowdown') {
            return '↓';
          } else if (s === 'arrowleft') {
            return '←';
          } else if (process.platform === 'darwin' && s === 'alt') {
            return '⌥';
          } else {
            return s.charAt(0).toUpperCase() + s.slice(1);
          }
        }).join('+');
      } else {
        return '';
      }
    },
  },
};
</script>
