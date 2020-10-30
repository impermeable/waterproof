<script>
export default {
  name: 'FileInteraction',
  methods: {
    /**
     * Shows a dialog for selecting a save location, and then
     * saves the opened notebook into the chosen file.
     */
    saveAsFile: function() {
      // First, get the desired file path
      const options = this.notebook.exerciseSheet ? {
        defaultPath: 'untitled.wpe',
        filters: [
          {
            name: 'Waterproof Exercise Sheet',
            extensions: ['wpe'],
          },
        ],
      } : {
        defaultPath: 'untitled.wpn',
        filters: [
          {
            name: 'Waterproof Notebook',
            extensions: ['wpn'],
          },
        ],
      };

      const {dialog} = require('electron').remote;
      const filePath = dialog.showSaveDialogSync(options);

      // Then, save the file like normal
      if (filePath) {
        this.notebook.filePath = filePath;
        this.notebook.write();
        this.$parent.$parent.addToRecentFileList(this.notebook.filePath);
      }

      // Then, reset the fileURI for the tab.
      this.$parent.$parent.setTabURI(this.index, this.notebook.filePath);
    },

    /**
     * Saves the opened notebook at its filepath
     * If this filepath is not specified yet, the save as method
     * is used to let the user choose a path.
     */
    saveFile: function() {
      if (!this.notebook.filePath || this.notebook.filePath === 'Tutorial') {
        this.saveAsFile();
      } else {
        this.notebook.write();
        this.$parent.$parent.addToRecentFileList(this.notebook.filePath);
      }
    },

    saveDialogBeforeExport: function() {
      const {dialog} = require('electron').remote;
      if (this.notebook.unsavedChanges) {
        const dialogOptions = {
          type: 'info', title: 'Waterproof',
          buttons: ['Yes', 'No'],
          message: `Would you like to save the notebook before exporting?`,
        };
        if (dialog.showMessageBox(dialogOptions) === 0) {
          this.saveFile();
        }
      }
    },

    /**
     * Asks the user to specify a path, and saves the notebook
     * as a coq file at this location.
     */
    exportToCoq: function() {
      this.saveDialogBeforeExport();

      const {dialog} = require('electron').remote;

      const options = {
        defaultPath: 'untitled',
        title: 'Export to Coq file',
        filters: [
          {
            name: 'Coq file',
            extensions: ['v'],
          },
          {
            name: 'All files',
            extensions: ['*'],
          },
        ],
      };

      const filename = dialog.showSaveDialogSync(options);
      if (filename) {
        this.notebook.exportToCoq(filename);
      }
    },

    /**
     * Asks the user to specify a path, and saves the notebook
     * as an exercise at this location.
     */
    exportToExerciseSheet: function() {
      // Make sure we cannot export an exercise sheet
      if (this.notebook.exerciseSheet) {
        return;
      }

      this.saveDialogBeforeExport();
      const {dialog} = require('electron').remote;
      const options = {
        defaultPath: 'exercise',
        title: 'Export to exercise sheet',
        filters: [
          {
            name: 'Waterproof Exercise Sheet',
            extensions: ['wpe'],
          },
          {
            name: 'All files',
            extensions: ['*'],
          },
        ],
      };

      const filename = dialog.showSaveDialogSync(options);
      if (filename) {
        this.notebook.exportToExerciseSheet(filename);
      }
    },

    /**
     * Compile the standard waterproof libraries
     */
    compilewplib: function() {
      this.$store.dispatch('compileLibraries', true);
    },
  },
};
</script>
