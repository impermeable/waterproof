<script>
export default {
  name: 'CodeExecution',
  methods: {
    /**
     * Returns the three intervals corresponding to the parts of the code that
     * are executed, executing, and pending.
     * @param {Boolean} extendIntervals if true, the 'executed' interval will
     *  be extended at the end to touch the start of the 'executing' interval
     *  and the pending interval will be extended at the front to touch the
     *  end of the pending interval. This way, the three returned intervals
     *  together are continuous. Default is true.
     * @return {Object} an object of the form
     * {
     *    executed: {start, end},
     *    executing: {start, end},
     *    pending: {start, end},
     * }
     * where all the intervals {start, end} are with `start` inclusive, `end`
     * exclusive
     */
    getStatusIntervals: function(extendIntervals = true) {
      const state = this.coq.getState();
      // Edge case: if the document is empty,
      // nothing is executed/executing/pending

      if (state.sentenceSize() === 0
        || !this.executedUpTo
        || this.executedUpTo < 0) {
        return {executed: null, executing: null, pending: null};
      }
      // Compute what interval of characters that is executed
      const executed = {
        start: state.beginIndexOfSentence(0),
        end: this.executedUpTo,
      };
      // Take the first unexecuted sentence. If it does not exist or starts
      // after what is still pending, then we are done so only executed is
      // non-null
      const executingSentence =
        (state.sentenceAfterIndex(this.executedUpTo) || {}).index;
      if (executingSentence == null
        || state.beginIndexOfSentence(executingSentence) > this.pendingUpTo) {
        return {executed, executing: null, pending: null};
      }
      const executing = {
        start: executingSentence.sentence.beginIndex,
        end: executingSentence.sentence.endIndex,
      };

      if (extendIntervals) {
        // If enabled, drag the `executed` out to meet the executing part
        executed.end = executing.start;
      }

      const firstPendingSentence = state.sentenceAfterIndex(executing.end);
      if (firstPendingSentence === null || this.pendingUpTo === null) {
        return {executed, executing, pending: null};
      }

      // Crop pendingUpTo to the last whole sentence
      let lastPendingLine = state.sentenceBeforeIndex(this.pendingUpTo);
      if (lastPendingLine == null || lastPendingLine === -1) {
        return {executed, executing, pending: null};
      }

      lastPendingLine = state.getSentenceByIndex(lastPendingLine);

      const pending = {
        start: firstPendingSentence.sentence.beginIndex,
        end: lastPendingLine.endIndex,
      };

      if (extendIntervals) {
        // If enabled, make the pending interval start right after the executing
        pending.start = executing.end;
      }

      return {executed, executing, pending};
    },
    refreshExecStatus: function(animation = true) {
      this.setGutterHeight();
      this.clearCodeDecorations();
      const {executed} = this.getStatusIntervals();
      if (!executed) {
        this.executed = false;
        this.execHeight = 0;
        this.execHeightBall = 0;
        return;
      }

      this.$nextTick(() => {
        this.executed = true;

        const execPos = this.findCodeIndex(executed.end, true);
        const {blockIndex, posInBlock} = execPos;

        this.blocks[blockIndex].state.executedUpTo = posInBlock;

        // Draw the line
        this.$nextTick(() => {
          // TODO: there must be a better way to do this. Right now, I request
          // the position of the tick icon on the screen (which doesn't exist
          // until after the next refresh, hence $nextTick), and subtract the
          // top position of the editing pane to find the desired length of the
          // execution gutter.

          this.alignGutter(animation);
        });
      });
    },
  },
};
</script>
