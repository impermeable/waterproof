<template>
    <div class="messages-window">
        <div class="message-header">
            <h3>Messages</h3>
            <span class="clear-messages-button" @click="clear">
                <img src="../../../assets/images/trash-solid.svg"
                     alt="Clear all" height="20px">
            </span>
        </div>
        <div class="messages" v-if="ready">
            <div class="message message-error"
                 v-if="addError.message && showingAddError">
                <span class="messageText">
                    {{addError.message}}
                </span>
            </div>
            <div class="message"
                 v-for="(message, index) in messages" :key="message + index">
                <span class="messageText">
                    {{message.text}}
                </span>
                <a @click="removeMessage(index)" title="Remove message">
                    <div class="clear-message"></div>
                </a>
            </div>
        </div>
        <div style="text-align: center" v-else>
            <span>
                Loading Coq
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
    clear: function() {
      this.messages = [];
    },
    addMessage: function(message) {
      this.messages.push({
        text: message,
      });
    },
    removeMessage: function(index) {
      this.messages.splice(index, 1);
    },
    forceAddError: function() {
      clearTimeout(this.showTimeout);
      this.showingAddError = true;
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
    .messages-window {
        flex-basis: 50%;
        min-height: 100px;
        flex-grow: 1;
        position: relative;
        border-bottom: 1px solid $color-primary-light;
    }

    .clear-messages-button {
        display: flex;
        justify-content: center;
        align-items: center;
        width: 40px;
        transition: 0.3s;
        &:hover {
            background-color: $color-primary-dark;
            cursor: pointer;
        }
    }

    .messages {
        height: calc(100% - 2em);
        padding: 0.2em 0;
        overflow-y: auto;

    }

    .message-header {
        display: flex;
        flex-flow: row nowrap;
        justify-content: space-between;
        height: 40px;
        background: $color-primary-light;
        color: $color-on-primary;
        padding-left: 5px;
    }

    .message {
        margin: 0 19px;
        border-bottom: 1px solid gray;
        position: relative;

        .clear-message {
            position: absolute;
            top: 8px;
            right: -16px;
            width: 15px;
            height: 15px;

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
                color: $color-primary-dark;
                cursor: pointer;
            }
        }
    }

    .message-error {
        border: 3px solid red;
        background: red;
        color: white;
    }

    .load-dot {
        animation: 0.9s blink step-end infinite;
        color: black;
        margin-left: -4px;
    }

    @keyframes blink {
        from, to {
            color: transparent;
        }
        50% {
            color: black;
        }
    }

</style>
