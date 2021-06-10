<template>
    <div class="messages-window">
        <div class="response-header">
            <h3>Messages</h3>
            <span class="clear-messages-button" @click="clear">
                <img src="../../../assets/images/trash-solid.svg"
                     alt="Clear all" class="trash-icon">
            </span>
        </div>
        <div class="messages" v-if="ready"
             ref="messagesBox">
            <div class="message message-error"
                 v-if="haveAddError && showingAddError">
                <span class="messageText">
                    {{addErrorText}}
                </span>
            </div>
            <div class="message highlight"
                 style="animation-name: blinkColors;"
                 @animationend="removeAnimation"
                 ref="messageElts"
                 v-for="(message, index) in messages"
                 :key="message.text + index" >
                <span :class="{'messageText': true,
                'repeated-message': message.deprecated}">
                    {{message.text}}
                </span>
                <a @click="removeMessage(index)" title="Remove message">
                    <div class="clear-message"></div>
                </a>
            </div>
        </div>
        <div style="text-align: center" v-else>
            <span>
                Loading
            </span>
            <span class="load-dot" style="animation-delay: 0s">
                .
            </span>
            <span class="load-dot" style="animation-delay: 0.15s">
                .
            </span>
            <span class="load-dot" style="animation-delay: 0.3s">
                .
            </span>
        </div>
    </div>
</template>

<script>
const ignoredErrors = [
  // 'Nested proofs are not allowed unless you ' +
  //   'turn option Nested Proofs Allowed on',
].map((s) => s.toLowerCase());

export default {
  name: 'MessagesWindow',
  props: {
    eventBus: {},
    ready: Boolean,
    addError: {},
    addErrorTimeout: {
      type: Number,
      default: 1500,
    },
  },
  data: function() {
    return {
      messages: [],
      showingAddError: false,
      showTimeout: null,
    };
  },
  created: function() {
    this.eventBus.$on('clear-messages', this.clear);
    this.eventBus.$on('on-coq-message', this.addMessage);
    this.eventBus.$on('coqTo', this.forceAddError);
    this.eventBus.$on('coqAll', this.forceAddError);
    this.eventBus.$on('coqNext', this.forceAddError);
  },
  methods: {
    removeAnimation: function(e) {
      e.target.style.animationName = '';
    },
    clear: function() {
      this.messages = [];
    },
    addMessage: function(message) {
      if (Object.prototype.hasOwnProperty.call(message, 'text')) {
        for (let i = this.messages.length - 1; i >= 0; --i) {
          const oldMessage = this.messages[i];
          if (oldMessage.id === message.id) {
            if (oldMessage.text === message.text) {
              this.$refs.messageElts[i].scrollIntoView({
                behavior: 'smooth',
                block: 'start',
              });
              this.$refs.messageElts[i].style.animationName = 'blinkColors';
              return;
            }
          }
        }
        this.messages.push({
          text: message.text,
          id: message.id,
          deprecated: false,
        });
      } else {
        // Assume old style message
        this.messages.push({
          text: message,
          id: null,
          deprecated: false,
        });
      }
      if (typeof(requestAnimationFrame) !== 'undefined') {
        requestAnimationFrame(() => {
          this.$refs.messagesBox.scrollTop =
              this.$refs.messagesBox.scrollHeight;
        });
      }
    },
    removeMessage: function(index) {
      this.messages.splice(index, 1);
    },
    forceAddError: function() {
      clearTimeout(this.showTimeout);
      this.showingAddError = true;
    },
  },
  computed: {
    haveAddError() {
      const message = this.addError.message;
      if (!message) {
        return false;
      }
      const text = message.message.toLowerCase();
      for (const err of ignoredErrors) {
        if (text.includes(err)) {
          return false;
        }
      }
      return true;
    },
    addErrorText() {
      if (!this.haveAddError) {
        return '';
      }
      let message = this.addError.message.message.trim();
      if (message.startsWith(',')) {
        message = message.substring(1);
      }
      if (message.includes('Nested proofs are not allowed unless you ' +
        'turn option Nested Proofs Allowed on')) {
        message += ` (Did you forget a 'Qed.' ?)`;
      }
      return message;
    },
  },
  watch: {
    addError(newValue) {
      clearTimeout(this.showTimeout);
      this.showingAddError = false;
      if (newValue != null) {
        if (this.addErrorTimeout > 0) {
          this.showTimeout = setTimeout(() => {
            this.showingAddError = true;
          }, this.addErrorTimeout);
        } else {
          // bit strange but allows for no timeout (also for testing)
          this.showingAddError = true;
        }
      }
    },
  },
};
</script>


<style lang="scss" scoped>
  @import "../../../assets/sass/_colors.scss";
    .message {
        margin: 0 19px;
        border-bottom: 1px solid gray;
        position: relative;
        word-break: break-word;

        .clear-message {
            position: absolute;
            top: 8px;
            right: -16px;
            width: 15px;
            height: 15px;

            // TODO: Somehow make this part work with theming?
            $cross-lines-color: $color-primary;
            $cross-background-color: $color-on-primary;

            border: 1px $cross-background-color solid;


            background:
                    linear-gradient(45deg,
                            transparent 0%,
                            transparent 43%,
                            $cross-lines-color 45%,
                            $cross-lines-color 55%,
                            transparent 57%,
                            transparent 100%),
                    linear-gradient(135deg,
                            $cross-background-color 0%,
                            $cross-background-color 43%,
                            $cross-lines-color 45%,
                            $cross-lines-color 55%,
                            $cross-background-color 57%,
                            $cross-background-color 100%);

            &:hover {
                @include theme(color, color-primary-dark);
                cursor: pointer;
            }
        }
    }

    .message-error {
      @include theme(border, color-error, 3px solid);
      @include theme(background-color, color-error);
      @include theme(color, color-error-text);
    }

    .load-dot {
        animation: 0.9s blink step-end infinite;
        @include theme(color, color-black);
        margin-left: -4px;
    }

    // TODO understand how to map this to a theme
    @keyframes blink {
        from, to {
            color: transparent;
        }
        50% {
            color: black;
        }
    }

    .highlight {
      background: transparent;
      //animation-name: blinkColors;
      animation-iteration-count: 1;
      animation-timing-function: ease-in;
      animation-duration: 1s;
    }

    .repeated-message {
      text-decoration: line-through;
    }

</style>

<style lang="scss">
// TODO understand how to map this to a theme
@keyframes blinkColors {
  0% {
    background: $color-primary-light;
    color: $color-on-primary;
  }
  100% {
    background: transparent;
    color: inherit;
  }
}
</style>
