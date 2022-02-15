const fs = require('fs');

const DEFAULT_BLACKLIST = [
  // commands that allow introducing theorems without proof
  'Parameter',
  'Parameters',
  'Axiom',
  'Axioms',
  'Conjecture',
  'Conjectures',
  'Variable',
  'Variables',
  'Hypothesis',
  'Hypotheses',
  'Admitted',
  // commands that mess with the order/state of execution
  'Undo',
  'Restart',
  'BackTo',
  'Back',
  'Reset',
  'Quit',
  'Drop',
];

// Vernacular commands that mostly just print messages
// TODO: figure out what to do with this
// const VERNAC_COMMANDS = [
//   'About',
//   'Check',
//   'Eval',
//   'Extraction',
//   'Inspect',
//   'Locate',
//   'Obligations',
//   'Print',
//   'Pwd',
//   'Recursive Extraction',
//   'Search',
//   'Show',
//   'Test',
// ];

/** Class containing the internal representation of a notebook file. */
class Notebook {
  /** Constructor of the notebook. */
  constructor() {
    this.blocks = [];
    this.exerciseSheet = false;
    this.filePath = '';
    this.commandBlacklist = new Set();
    this.unsavedChanges = false;
  }

  /**
   * Reset this notebook
   * (Clears all blocks and makes it a non exercise sheet)
   */
  clearContent() {
    this.blocks = [];
    this.exerciseSheet = false;
    this.commandBlacklist = new Set();
  }

  /**
   * @return {string} the filename corresponding to this notebook or 'untitled'
   * if the notebook is not from a file
   */
  getName() {
    if (this.filePath) {
      return this.filePath.split('\\').pop().split('/').pop();
    } else {
      return 'untitled';
    }
  }

  /**
   * Creates a new code block
   *
   * @param {String} text Text content of the added block.
   * @param {Boolean} inInputField Whether this is an input field.
   * @return {Object} The code block
   */
  createCodeBlock(text, inInputField) {
    return {
      type: 'code',
      text: text,
      state: {
        done: false,
        error: null,
        inInputField: inInputField,
        textIndex: -1,
        foldStatus: {
          isFolded: false,
          startFold: false,
          endBlock: null,
        },
        isSelected: false,
      },
    };
  }

  /**
   * Creates a new text block
   *
   * @param {String} text Text content of the added block.
   * @param {Boolean} inInputField boolean stating whether this block is
   * inside an input field.
   * @return {Object} The text block
   */
  createTextBlock(text, inInputField) {
    return {
      type: 'text',
      text: text,
      state: {
        inInputField: inInputField,
        foldStatus: {
          isFolded: false,
          startFold: false,
          endBlock: null,
        },
        isSelected: false,
      },
    };
  }


  /**
   * Creates a new hint block
   * @param {String} text Text content of the hint
   * @return {Object} the hint block
   */
  createHintBlock(text) {
    return {
      type: 'hint',
      text: 'Click to open hint.\n<hint>\n' + text,
      state: {
        foldStatus: {
          isFolded: false,
          startFold: false,
          endBlock: null,
        },
        isSelected: false,
      },
    };
  }

  /**
   * Create input blocks
   * @param {String} id The name/id of this input field
   * @return {Array} The blocks
   */
  createInputArea(id) {
    const blocks = [];
    blocks.push(this.createInputBlock(id, true));
    blocks.push(this.createInputBlock(id, false));
    return blocks;
  }

  /**
   * Create input block
   * @param {String} id The name/id of this input field
   * @param {Boolean} start Whether this block is a start block
   * @return {Block} The input block
   */
  createInputBlock(id, start) {
    return {
      type: 'input',
      start: start,
      id: id,
      state: {
        foldStatus: {
          isFolded: false,
          startFold: false,
          endBlock: null,
        },
        isSelected: false,
      },
    };
  }

  /**
   * Split a part of a block into a new block
   *
   * @param {Integer} index The block to (potentially) split
   * @param {Integer} from From selection
   * @param {Integer} to To selection
   * @param {String} newType Type of new block
   * @return {Array} Blocks to put back
   */
  splitBlock(index, from, to, newType) {
    const block = this.blocks[index];
    if (block.type === 'input') {
      if (block.start) {
        return [block, this.createBlock(newType, '', true)];
      } else {
        return [this.createBlock(newType, '', true), block];
      }
    }

    const textLength = block.text.length;

    if (from === 0 && to === textLength) {
      // full selection
      return [this.createBlock(newType, block.text, block.state.inInputField)];
    }

    const newBlock = this.createBlock(newType,
        block.text.substring(from, to),
        block.state.inInputField);

    let preBlock = null;
    let postBlock = null;

    if (from > 0) {
      preBlock = this.createBlock(block.type,
          block.text.substring(0, from),
          block.state.inInputField);
    }

    if (to < textLength) {
      postBlock = this.createBlock(block.type,
          block.text.substring(to),
          block.state.inInputField);
    }

    return [
      preBlock,
      newBlock,
      postBlock,
    ].filter((b) => b !== null);
  }


  /**
   * Create block based on string name
   * @param {String} type the type of the block
   * @param {String} text the text in the block
   * @param {Boolean} inInput whether the block is in an inputfield
   * @return {Object} the block
   */
  createBlock(type, text, inInput=false) {
    if (type === 'code') {
      return this.createCodeBlock(text, inInput);
    } else if (type === 'text') {
      return this.createTextBlock(text, inInput);
    } else if (type === 'hint') {
      return this.createHintBlock(text);
    } else {
      return null;
    }
  }

  /**
   * Setter for the file path.
   *
   * @param {String} filePath The filepath that needs to be set
   */
  setFilePath(filePath) {
    this.filePath = filePath;
  }

  /**
   * Converts the internal object to text
   *
   * @param {Boolean} hints option to leave in hints
   * @param {Boolean} textblocks option to leave in text blocks
   * @param {Boolean} coqcode option to leave in Coq code
   * @return {String} text that will be displayed
   */
  parseToText(hints = true, textblocks = true, coqcode = true) {
    return wpToCoq(this.blocks);
  }

  /**
   * Saves the notebook to the file specified by its file path
   * @param {function} onFileWritten the callback when saving is done
   * @param {function} onFileError the callback when saving fails
   */
  write(onFileWritten, onFileError) {
    this.unsavedChanges = false;
    onFileWritten = onFileWritten || (() => {});
    onFileError = onFileError || (() => {});

    // Clone the object
    const blockCopy = JSON.parse(JSON.stringify(this.blocks));
    for (const block of blockCopy) {
      delete block.state;
    }

    // When saving, turn the blacklist into a list for JSON
    const obj = {
      exerciseSheet: this.exerciseSheet,
      blocks: blockCopy,
    };

    if (this.exerciseSheet && this.commandBlacklist !== DEFAULT_BLACKLIST) {
      obj.commandBlacklist = [...this.commandBlacklist];
    }
    const notebookString = JSON.stringify(obj, null, 2);
    fs.writeFile(this.filePath, notebookString, (err) => {
      if (err) {
        onFileError(err);
        throw err;
      }
      onFileWritten();
    });
  }

  /**
   * Read a Waterproof file and set the data.
   *
   * @param {Function} onFileRead callback when file is read
   * @param {Function} onFileError callback when error in reading file
   */
  read(onFileRead, onFileError) {
    onFileRead = onFileRead || (() => {});
    onFileError = onFileError || (() => {});

    let realFilePath = this.filePath;

    if (this.filePath === 'Tutorial') {
      if (process.env.NODE_ENV === 'production') {
        const path = require('path');
        realFilePath =
            path.join(__dirname, '../../wrapper/assistance/', 'Tutorial.wpe');
      } else {
        realFilePath = './wrapper/assistance/Tutorial.wpe';
      }
    }

    fs.readFile(realFilePath, (err, data) => {
      if (err) {
        this.clearContent();
        onFileError(err);
        return;
      }

      try {
        this.clearContent();
        const read = JSON.parse(data);

        // this needs to be done before adding them to data
        // otherwise Vue can't detect them and they won't be reactive
        // maybe do this in a 'reviver'
        let inInputField = false;
        for (const block of read.blocks) {
          Notebook.setDefaultBlockState(block, inInputField);
          if (block.type === 'input' && block.start) {
            inInputField = true;
          }
          if (block.type === 'input' && !block.start) {
            inInputField = false;
            block.state.inInputField = false;
          }
          this.blocks.push(block);
        }

        this.exerciseSheet = read.exerciseSheet;

        // Read the command blacklist. Also parse from list to Set, since JSON
        // does not allow sets.
        if (this.exerciseSheet) {
          if (read.commandBlacklist) {
            this.commandBlacklist = new Set(read.commandBlacklist);
          } else {
            this.commandBlacklist = DEFAULT_BLACKLIST;
          }
        }
      } catch (error) {
        onFileError(error);
        throw error;
      }

      onFileRead();
    });
  }

  /**
   * Create the default state for a block
   * @param {Object} block the block
   * @param {Boolean} inInputField whether it is in an input field
   */
  static setDefaultBlockState(block, inInputField = false) {
    block.state = {};
    block.state.inInputField = inInputField;
    block.state.isSelected = false;
    block.state.foldStatus= {
      isFolded: false,
      startFold: false,
      endBlock: null,
    };
    if (block.type === 'code') {
      block.state.done = false;
      block.state.error = null;
    }
  }

  /**
   * Exports the notebook to a Coq file.
   *
   * @param {String} filename Containing the filepath of the file
   * @param {function} onExported callback when the exporting is finished
   * @param {function} onError callback when an error occurs
   */
  exportToCoq(filename, onExported, onError) {
    fs.writeFile(filename, this.parseToText(), (err) => {
      if (err) {
        onError(err);
        throw err;
      }
      if ( onExported ) {
        onExported();
      }
    });
  }

  /**
   * Exports the notebook to an exercise sheet
   *
   * @throws {Error} when the notebook is already an exercise sheet
   * @param {String} filename The filepath for saving the exercise sheet
   * @param {function} onExported Callback when the exporting is finished
   * @param {function} onError Callback when an error occurs
   */
  exportToExerciseSheet(filename, onExported, onError) {
    onExported = onExported || (() => {});
    onError = onError || (() => {});
    if (this.exerciseSheet) {
      onError(Error(
          'An exercise sheet cannot be exported to an exercise sheet'));
    }

    const copy = new Notebook();
    copy.blocks = JSON.parse(JSON.stringify(this.blocks));

    copy.blocks = this.removeProofs(copy.blocks);

    copy.exerciseSheet = true;
    copy.commandBlacklist = DEFAULT_BLACKLIST;
    copy.setFilePath(filename);
    copy.write(onExported, onError);
  }


  /**
   * In an input block: remove code blocks, and places one admitted
   *
   * @param {Array} inputBlocks blocks to remove sections from
   * @return {Array} of transformed blocks
   */
  removeProofs(inputBlocks) {
    // We scan over the notebook once, and keep track of
    // whether we are in an input block
    let inInputBlock = false;

    // We create a new list of blocks that will form the exercise sheet
    const blocks = [];
    for (let i = 0; i < inputBlocks.length; i++) {
      const block = inputBlocks[i];

      // Keep track of whether we are in an input block
      if (block.type === 'input') {
        blocks.push(block);
        inInputBlock = block.start;

        // If we entered an input block, we add the Admitted.
        if (inInputBlock) {
          const admittedBlock = this.createCodeBlock('Admitted.');
          blocks.push(admittedBlock);
        }
      } else {
        if (!inInputBlock) {
          blocks.push(block);
        }
      }
    }
    return blocks;
  }

  /**
   * Imports a Coq file as a notebook.
   *
   * @param {String} filename Containing the filepath of the file
   * @param {Boolean} formatCoqComments whether to put all coq comments in text
   *  blocks
   */
  importFromCoq(filename, formatCoqComments=true) {
    const callback = (err, data) => {
      if (err) {
        throw err;
      }

      const coqText = data.toString();
      if (!formatCoqComments) {
        this.blocks = [
          this.createCodeBlock(coqText),
        ];
      } else {
        this.blocks = coqToWp(coqText);
      }
    };

    fs.readFile(filename, callback);
  }

  /**
   * Cuts a string up in an array of strings. The cut points are
   * exactly at the beginning of the matches of the regular expression keywords
   * @param {String} string the string that needs to be cut up in pieces
   * @param {RegExp} keywords the regular expression used to select the keywords
   * @return {Array} An array with the pieces of the cut up string
   */
  cutStringBetweenKeywords(string,
      keywords=/Lemma|Theorem|Proof|Definition|Tactic|Ltac/) {
    const stringPieces = [];

    let stringLeft = string;
    let endPos = 1 + stringLeft.substring(1).search(keywords);
    while (endPos > 0) {
      stringPieces.push(stringLeft.substring(0, endPos).trim());
      stringLeft = stringLeft.substring(endPos);
      endPos = 1 + stringLeft.substring(1).search(keywords);
    }
    const tail = stringLeft.trim();
    if (tail.length > 0) {
      stringPieces.push(tail);
    }

    return stringPieces;
  }
}

export default Notebook;

/**
 * Convert text to never break a Coq comment
 * @param {string} text
 * @return {string}
 */
function createSafeCoqComment(text) {
  return text.replaceAll('*)', '*💧)')
      .replaceAll('(*', '(💧*')
      .replaceAll('"', '""');
}

/**
 * Revert the changes made by createSafeCoqComment
 * @param {string} text
 * @return {string}
 */
function revertSafeCoqComment(text) {
  return text.replaceAll('*💧)', '*)')
      .replaceAll('(💧*', '(*')
      .replaceAll('""', '"');
}

/**
 * Small class to wrap errors
 */
class ImportError extends Error {
  // eslint-disable-next-line require-jsdoc
  constructor(message) {
    super(message);
    this.name = 'ImportError';
  }
}

/**
 * Converts coq code to a notebook format
 * This does not convert back any waterproof things and just puts all
 * special comments in text blocks and the rest in code blocks.
 * @param {String} coqCode the input code
 * @return {Array} the blocks from the code
 */
function coqToWp(coqCode) {
  const blocks = []; // return array
  const blockStrings = coqCode.split('(*💧'); // seperate block strings
  // The first part after .split is the empty space before the first block start
  if (blockStrings.shift().trim() !== '') {
    throw new ImportError('Did not start with a block.');
  }
  let inInputField = false;
  for (let i = 0; i < blockStrings.length; i++) {
    const blockString = blockStrings[i];
    const dataEnd = blockString.indexOf('*)');
    const dataString = blockString.substring(0, dataEnd);
    // should contain type and possibly start and id
    const block = JSON.parse(dataString);
    Notebook.setDefaultBlockState(block, inInputField);
    if (block.type !== 'input') {
      // get text part, so skip '*)\n' which is 3 chars.
      let textString = blockString.substring(dataEnd + 3);
      if (i !== blockStrings.length - 1) {
        // removing trailing \n, which was added by join.
        textString = textString.substring(0, textString.length -1);
      }
      if (block.type !== 'code') {
        // remove everything around [text] of (*[text]*) revert [text]
        textString = textString.substring(2, textString.length -2);
        textString = revertSafeCoqComment(textString);
      }
      block.text = textString;
    } else {
      inInputField = block.start;
    }
    blocks.push(block);
  }
  return blocks;
}

/**
 * Convert blocks into coq parsable text, following specification.md
 * @param {[]} blocks the list of blocks
 * @return {string} the coq text
 */
function wpToCoq(blocks) {
  const blockStrings = [];
  for (const block of blocks) {
    let data = {type: block.type};
    if (block.type === 'input') {
      data.start = block.start;
      data.id = block.id;
    }
    data = '(*💧' + JSON.stringify(data) + '*)';
    if (block.type !== 'input') {
      let text = block.text;
      if (block.type !== 'code') {
        text = '(*' + createSafeCoqComment(text) + '*)';
      }
      data = data + '\n' + text;
    }
    blockStrings.push(data);
  }
  return blockStrings.join('\n');
}

export {coqToWp, wpToCoq};
