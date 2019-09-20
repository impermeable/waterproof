<script>
import SerapiCommands from '../../../coq/serapi/SerapiCommands';
import CoqSerapi from '../../../coq/serapi/CoqSerapi';
import TCPManager from '../../../coq/serapi/workers/TCPManager';

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
      targetIndex: -1,
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
    this.eventBus.$on('coqTo', this.coqTo);
    this.eventBus.$on('coqAll', this.coqAll);
    this.eventBus.$on('coqAST', this.coqAST);
  },
  methods: {
    startCoq: function() {
      // const worker = new SerapiWorkerJs('jscoq-builds/sertop_js.js');
      this.$store.dispatch('getSertopPath').then((sertopPath) => {
        const worker = this.socket.createNewWorker(sertopPath);
        this.coq = new CoqSerapi(
            new SerapiCommands(worker,
                this.message, this.onReady), this);
        this.eventBus.$emit('clear-messages');
        this.goals = '';
      }, () => {
        console.err('error in reading config file');
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
      this.coq.executeNext().then();
    },

    /**
     * Reverts the execution of the last executed coq sentence
     */
    coqPrev: function() {
      // When reverting, make sure nothing is marked as pending
      this.targetIndex = null;
      this.coq.executePrevious().then();
    },

    /**
     * Executes all coq sentences up to the current cursor position
     */
    coqTo: function() {
      const targetIndex = this.findCodeIndex();
      this.coq.executeTo(targetIndex).then();
      this.targetIndex = targetIndex;
    },

    /**
     * Executes all coq sentences in the code blocks
     */
    coqAll: function() {
      const targetIndex = this.coqCode.length;
      this.coq.executeTo(targetIndex).then();
      this.targetIndex = targetIndex;
    },

    /**
     * Request the Abstract Syntax Tree (ast) for given sentence
     *
     * @param {Number} sentenceNr  The sentence to request the AST for
     */
    coqAST: function(sentenceNr) {
      this.coq.getAST(sentenceNr);
    },

    coqSearch: function(detail) {
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
      this.addError = {message: error, index: errorIndex};
    },

    executeStarted: function(index) {
      this.startedExecutionIndex = index;
    },
  },
  beforeDestroy() {
    this.coq.stop();
  },
};
</script>
