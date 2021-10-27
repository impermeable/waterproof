<template>
  <li class="recent-file"
      :title="fileInfo.location"
      @click="openRecentFile(fileInfo)">
      {{ fileInfo.name }}
  </li>
</template>

<script>

import Index from '../Index';
import Notebook from '../../io/notebook';

const {dialog} = require('electron').remote;

export default {
  name: 'RecentFile',
  props: ['fileInfo'],
  components: {
    Index,
  },
  data: function() {
    return {
      upHere: true,
    };
  },
  methods: {
    openRecentFile: function(fileInfo) {
      const location = fileInfo.location;
      const notebook = new Notebook();
      notebook.setFilePath(location);
      notebook.read(() => {
        this.$router.push({name: 'edit', query: {location}});
      }, (e) => {
        let dialogOptions;
        if (e instanceof SyntaxError) {
          // File parsing failed
          dialogOptions = {type: 'info', title: 'Waterproof',
            buttons: ['Yes', 'Cancel'],
            message: `The file you attempted to open is not a valid ` +
              `notebook.\nDo you want to remove this file from your recent ` +
              `file list?`,
          };
        } else {
          // File not found
          dialogOptions = {type: 'info', title: 'Waterproof',
            buttons: ['Yes', 'Cancel'],
            message: `The file you attempted to open no longer ` +
              `exists.\n` + `Do you want to remove this file from your ` +
              `recent files list?`,
          };
        }
        if (dialog.showMessageBoxSync(dialogOptions) === 0) {
          this.$parent.recents.removeFileListEntry(fileInfo.location);
        }
      });
    },
  },
};
</script>

<style lang="scss">
@import '../../assets/sass/_colors.scss';
.recent-file {
  padding: 0.5rem;
  list-style: none;
  cursor: pointer;

  &:hover {
    @include theme(background-color, color-primary-light);
    border-radius: 5px;
  }

  &:first-child {
    margin-top: 0.5rem;
  }

  &:last-child {
    margin-bottom: 0.5rem;
  }
}
</style>
