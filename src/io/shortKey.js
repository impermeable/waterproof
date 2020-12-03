let defaultShortKeys;
if (process.platform === 'darwin') {
  defaultShortKeys = {
    executeNext: ['alt', 'arrowdown'],
    executePrev: ['alt', 'arrowup'],
    executeToCursor: ['alt', 'arrowright'],
    executeAll: ['alt', 'end'],

    insertCode: ['ctrl', 'c'],
    insertText: ['ctrl', 't'],
    insertHint: ['ctrl', 'h'],
    insertInputArea: ['ctrl', 'i'],
    tutorialPage: {},

    newFile: ['meta', 'n'],
    loadFile: ['meta', 'o'],
    saveFile: ['meta', 's'],
    saveAsFile: ['f12'],
    exportToCoq: ['ctrl', 'e'],
    importFromCoq: {},
    exportToExerciseSheet: ['meta', 'e'],
    closeTab: ['meta', 'w'],

    undo: ['meta', 'z'],
    redo: ['meta', 'y'],
    findAndReplace: ['meta', 'f'],
    toggleFocusInputs: ['ctrl', 'g'],

    zoomIn: ['meta', 'plus'],
    zoomOut: ['meta', 'minus'],

    commonCommands: {},
    commonSymbols: {},
    commonTactics: {},

    cut: ['meta', 'x'],
    copy: ['meta', 'c'],
    paste: ['meta', 'v'],
    delete: ['del'],
    fold: ['ctrl', 'f'],
    selectAll: ['meta', 'a'],
    deselect: ['meta', 'd'],
  };
} else {
  defaultShortKeys = {
    executeNext: ['alt', 'arrowdown'],
    executePrev: ['alt', 'arrowup'],
    executeToCursor: ['alt', 'arrowright'],
    executeAll: ['alt', 'end'],

    insertCode: ['alt', 'c'],
    insertText: ['alt', 't'],
    insertHint: ['alt', 'h'],
    insertInputArea: ['alt', 'i'],
    tutorialPage: {},

    newFile: ['ctrl', 'n'],
    loadFile: ['ctrl', 'o'],
    saveFile: ['ctrl', 's'],
    saveAsFile: ['f12'],
    exportToCoq: ['alt', 'e'],
    importFromCoq: {},
    exportToExerciseSheet: ['ctrl', 'e'],
    closeTab: ['ctrl', 'w'],

    undo: ['ctrl', 'z'],
    redo: ['ctrl', 'y'],
    findAndReplace: ['ctrl', 'f'],
    toggleFocusInputs: ['ctrl', 'g'],

    zoomIn: ['ctrl', 'plus'],
    zoomOut: ['ctrl', 'minus'],

    commonCommands: {},
    commonSymbols: {},
    commonTactics: {},

    cut: ['ctrl', 'x'],
    copy: ['ctrl', 'c'],
    paste: ['ctrl', 'v'],
    delete: ['del'],
    fold: ['alt', 'f'],
    selectAll: ['ctrl', 'a'],
    deselect: ['ctrl', 'd'],
  };
}

/** Class representing the keyboard shortcuts */
class ShortKeys {
  /** Constructor */
  constructor() {
    this.storage = window.localStorage;
    this.shortKeys = JSON.parse(JSON.stringify(defaultShortKeys));
    this.read();
  }

  /** Reads the shortKeys from the shortKeysPath */
  read() {
    const parsedKeys = JSON.parse(this.storage.getItem('shortKeys'));
    if (parsedKeys) {
      for (const key in defaultShortKeys) {
        if (parsedKeys[key]) {
          this.shortKeys[key] = parsedKeys[key];
        }
      }
    }
  }

  /** Writes the shortKeys object to a JSON file */
  write() {
    this.storage.setItem('shortKeys', JSON.stringify(this.shortKeys));
  }

  /**
   * Resets the shortKeys object to the default
   */
  resetShortKeys() {
    this.shortKeys = JSON.parse(JSON.stringify(defaultShortKeys));
    this.write();
  }
}

export default ShortKeys;
