<script>
import TCPManager from '../../../coq/serapi/workers/TCPManager';
import {writeActivity} from '@/activity-log';

export default {
  name: 'CoqInteraction',
  props: {
    socket: TCPManager,
  },
  data: function() {
    return {
      ready: false,
      goals: '',
      coq: null,
      executedIndex: -1,
      startedExecutionIndex: -1,
      addError: {
        message: '',
        index: -1,
      },
    };
  },
  mounted: function() {
    this.eventBus.$on('coqSearch', this.coqSearch);
    this.eventBus.$on('coqNext', this.coqNext);
    this.eventBus.$on('coqPrev', this.coqPrev);
    this.eventBus.$on('coqToCursor', this.coqToCursor);
    this.eventBus.$on('coqTo', this.coqTo);
    this.eventBus.$on('coqAll', this.coqAll);
    this.eventBus.$on('coqAST', this.coqAST);
    this.eventBus.$on('coqLog', this.coqToggleLog);
    this.eventBus.$on('coqTime', this.coqToggleTiming);
  },
  methods: {
    startCoq: function() {
      return this.$store.dispatch('createCoqInstance', this).then((coq) => {
        this.coq = coq;
        this.eventBus.$emit('clear-messages');
        this.goals = '';
      }, (reason) => {
        console.log(`error in worker creation: ${reason}`);
      });
    },

    /**
     * Enables the execution buttons, aligns the gutter
     * and sends the current code to serapi
     */
    onReady: function() {
      this.ready = true;
      // When Coq is ready, update to enable the buttons for execute-next etc.
      this.coq.setContent(this.coqCode);
      this.eventBus.$emit('notebook-state-changed');
    },

    /**
     * Executes the next coq sentence
     */
    coqNext: function() {
      this.coq.executeNext().then((val) => {
        if (typeof val === 'object' && val.noSentenceToExecute === true) {
          writeActivity('coq-next-beyond-sentences', {
            file: this.notebook.filePath,
            tabIndex: this.index,
            executedIndex: this.executedIndex,
            addErrorIndex: this.addError.index,
          });
        }
      });
    },

    /**
     * Reverts the execution of the last executed coq sentence
     */
    coqPrev: function() {
      // When reverting, make sure nothing is marked as pending
      this.coq.executePrevious().then();
    },

    /**
     * Executes all coq sentences up to the current cursor position
     */
    coqToCursor: function() {
      const targetIndex = this.findCodeIndex();
      this.coq.executeTo(targetIndex).then();
    },

    /**
     * Execute to a index in the code
     * @param {Number} index the index in the code to execute to
     */
    coqTo: function(index) {
      this.coq.executeTo(index);
    },

    /**
     * Executes all coq sentences in the code blocks
     */
    coqAll: function() {
      const targetIndex = this.coqCode.length;
      this.coq.executeTo(targetIndex).then();
    },

    /**
     * Request the Abstract Syntax Tree (ast) for given sentence
     *
     * @param {Number} sentenceNr  The sentence to request the AST for
     */
    coqAST: function(sentenceNr) {
      this.coq.getAST(sentenceNr);
    },

    coqSearch: function({query: detail}) {
      if (!detail || detail === this.lastSearch) {
        this.$store.commit('openSideWindow', 0);
        return;
      }

      if (detail.endsWith('.')) {
        this.coq.query(detail);
        return;
      }
      this.lastSearch = detail;

      this.$store.commit('onSearchStarted');
      this.coq.getSearchResults(detail,
          (result) => {
            this.$store.commit('onSearchResult', result);
          },
          () => {
            this.$store.commit('onSearchEnded');
          },
      );
    },

    /**
     * To be called after successfully changing the content in serapi
     * Updates the goals if they changed, sets executed index, and
     * removes the addError if this is specified
     *
     * @param {String} goal  The new goals, or null when there is no change
     * @param {number} index  The new execution index
     * @param {boolean} removeAddError  Whether the addError should be removed
     */
    setContentSuccess: function(goal, index, removeAddError) {
      if (goal !== null) {
        this.goals = goal;
        this.executedIndex = index;
      }
      if (removeAddError) {
        this.addError = {
          message: '',
          index: -1,
        };
      }
    },

    /**
     * To be called after unsuccessfully changing the content in serapi
     * Stores the error in this.addError
     *
     * @param {string} error  The error message
     * @param {number} errorIndex  The index where the error occured
     */
    setContentError: function(error, errorIndex) {
      this.addError = {
        message: error,
        index: errorIndex,
        file: this.notebook.filePath,
        tabIndex: this.index,
      };
    },

    executeStarted: function(index) {
      this.startedExecutionIndex = index;
    },

    coqToggleLog: function() {
      if (this.coq.tagger) {
        this.coq.tagger.logging = !this.coq.tagger.logging;
      }
    },

    coqToggleTiming: function() {
      if (this.coq.tagger) {
        this.coq.tagger.timing = !this.coq.tagger.timing;
      }
    },
  },
  beforeDestroy() {
    this.coq.stop();
  },
};
</script>
