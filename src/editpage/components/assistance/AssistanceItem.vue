<script>
export default {
  props: {
    item: Object,
    hasPrevious: Boolean,
    eventBus: Object,
    showAdvanced: Boolean,
  },
  methods: {
    copyToClipboard: function(toCopy) {
      const {clipboard} = require('electron');
      clipboard.write({text: toCopy});
    },
    insertAtCursor: function(toInsert) {
      this.eventBus.$emit('insertAtCursor', toInsert);
    },
  },
};
</script>

<style lang="scss">
@import '../../../assets/sass/_colors.scss';
  .assistance-item {
    overflow-wrap: break-word;

    .content-and-copy {
      display: flex;
      justify-content: space-between;

      .title {
        font-weight: bold;
      }

      .insert-buttons {
        display: flex;
        flex-direction: column;
        justify-content: flex-start;
        align-items: center;
        margin-left: 10px;

        .button-insert {
          margin-top: 5px;
          cursor: copy;
          padding: 5px;
          width: 34px;
          height: 34px;

          &:hover {
            @include theme(background-color, color-gray-dark);
            border-radius: 10px;
          }
        }
      }
    }
  }

</style>
