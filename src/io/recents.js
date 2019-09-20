/** Class representing the recent file list */
class Recents {
  /** Constructor */
  constructor() {
    this.maxFileListLength = 10;
    this.filelist = [];
    this.storage = window.localStorage;
    this.read();
  }

  /** Reads the filelist from localstorage */
  read() {
    const parsedList = JSON.parse(this.storage.getItem('fileList'));
    if (parsedList) {
      this.filelist = parsedList;
    }
  }

  /** Writes the fileList object to a JSON file */
  write() {
    this.storage.setItem('fileList', JSON.stringify(this.filelist));
  }

  /** Removes all elements over the maxFileListLength */
  removeSurplus() {
    this.filelist = this.filelist.slice(0, this.maxFileListLength);
  }

  /**
   * Adds file list entry to the fileList object
   *
   * @param {String} location Contains the file location within the filesystem
   */
  addFileListEntry(location) {
    if (location === 'Tutorial') {
      return;
    }

    const entry = {};
    entry.location = location;
    entry.name = location.split(/[/\\]/).pop();

    // Remove all existing entries with the same file location
    this.removeFileListEntry(location);

    // Insert new entry at start of the list
    this.filelist.unshift(entry);

    // Remove any entries that are too old.
    this.removeSurplus();

    // Write to file
    this.write();
  }

  /**
   * Removes a file list entry based on the location
   *
   * @param {String} location Contains the file location within the filesystem
   */
  removeFileListEntry(location) {
    for (let i = this.filelist.length - 1; i >= 0; i--) {
      if (this.filelist[i].location === location) {
        this.filelist.splice(i, 1);
      }
    }
    this.write();
  }

  /**
   * Clears recent file list
   */
  clearRecentFileList() {
    this.filelist = [];
    this.write();
  }
}

export default Recents;
