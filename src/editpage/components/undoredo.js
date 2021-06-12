import Notebook from '../../io/notebook';

// The maximum allowed size of the undo and redo stacks
const MAX_BUFFER_SIZE = 10000;

/**
 * A class that deals with the editing of a notebook. It automatically modifies
 * the notebook using the given methods, and allows undoing and redoing commands
 * that were executed previously
 */
class UndoRedo {
  /**
   * Creates a new UndoRedo with empty undo and redo stacks
   * @param {Notebook} notebook the notebook that changes should be applied to
   */
  constructor(notebook) {
    this.undoStack = [];
    this.redoStack = [];
    this.notebook = notebook;
    this.commandGroup = null;
  }

  /**
   * Commands executed after this call will instead be added to a single
   * compound command, which can then be undone and redone as a single action
   */
  startGroup() {
    this.commandGroup = new CompoundCommand([]);
  }

  /**
   * This call ends the current compound command
   */
  endGroup() {
    if (this.commandGroup.commands.length > 0) {
      this.undoStack.push(this.commandGroup);
    }
    this.commandGroup = null;
  }

  /**
   * Executes a new command, that is not taken from the undo or redo stack
   * @param {Command} newCommand the command to execute
   */
  executeNewCommand(newCommand) {
    this.notebook.unsavedChanges = true;
    this.redoStack = [];

    let toExecute = newCommand;

    // See if `newCommand` can be merged with the last command
    const lastIndex = this.undoStack.length;
    if (lastIndex >= 0) {
      const last = this.undoStack[lastIndex - 1];
      const canBeMerged = canMerge(lastStep(last), lastStep(newCommand));
      if (canBeMerged) {
        last.reverse().execute(this.notebook);
        const mergedCommand = new CompoundCommand([
          last,
          newCommand,
        ]);
        this.undoStack.pop();
        toExecute = mergedCommand;
      }
    }

    toExecute.execute(this.notebook);

    if (this.commandGroup) {
      this.commandGroup.commands.push(toExecute);
    } else {
      this.undoStack.push(toExecute);
    }

    // Throw away some history if the undo stack is too large
    // Note that we don't need to do the same for the redo stack, or in other
    // methods, since this is the only point where te buffer can actually become
    // too large.
    while (this.undoStack.length > MAX_BUFFER_SIZE) {
      this.undoStack.shift();
    }
  }

  /**
   * Changes the text of a block, adding that command to the undo stack
   * @param {Number} index the index of the block whose text to change
   * @param {String} newText the desired text of the block
   */
  changeInput(index, newText) {
    // Problem: when the user types text and the text is updated, the CodeMirror
    // value also changes which fires a second event. This causes the undo-stack
    // items to be duplicated, and the redo-stack to be cleared on every change.
    // To avoid this, ignore change events when the text has not really changed.
    if (this.notebook.blocks[index].text === newText) {
      return;
    }
    this.executeNewCommand(
        new InputCommand(index, newText),
    );
  }

  /**
   * Inserts new blocks in the notebook
   * @param {Number} index the index at which to insert the blocks
   * @param {Array} blocks the blocks to insert
   */
  addBlocks(index, blocks) {
    // Edge case: allow a single block to be passed as well
    if (!Array.isArray(blocks)) {
      blocks = [blocks];
    }
    this.executeNewCommand(
        new AddBlocksCommand(index, blocks),
    );
  }

  /**
   * Removes blocks from the notebook
   * @param {Number} index the position at which to remove blocks
   * @param {Number} count the number of blocks to remove
   */
  removeBlocks(index, count) {
    this.executeNewCommand(
        new RemoveBlocksCommand(index, count),
    );
  }

  /**
   * Split block at index with given blocks
   * @param {Number} index the index
   * @param {Array} blocks the blocks into? which it was split
   */
  splitBlock(index, blocks) {
    // Create a compound command that removes the existing block and replaces it
    // with the three new block.
    const command = new CompoundCommand([
      new RemoveBlocksCommand(index, 1),
      new AddBlocksCommand(index, blocks),
    ]);
    this.executeNewCommand(
        command,
    );
  }

  /**
   * Undoes the last executed command if possible
   * @return {Boolean} true if a command was executed
   */
  undo() {
    // Pop a command from the undo stack, execute it, send it's reverse to the
    // redo stack
    if (this.undoStack.length === 0) {
      return false;
    } else {
      this.notebook.unsavedChanges = true;
      const lastCommand = this.undoStack.pop();
      const reverse = lastCommand.reverse();
      reverse.execute(this.notebook);
      this.redoStack.push(lastCommand);
      return true;
    }
  }

  /**
   * Redoes the last undone command if possible
   * @return {Boolean} true iff a command was executed
   */
  redo() {
    // Does the same as the undo() method, but with the stacks reversed
    if (this.redoStack.length === 0) {
      return false;
    } else {
      this.notebook.unsavedChanges = true;
      const lastCommand = this.redoStack.pop();
      lastCommand.execute(this.notebook);
      this.undoStack.push(lastCommand);
      return true;
    }
  }
}

/**
 * A command representing a change in input
 */
class InputCommand {
  /**
   * Creates a new InputCommand to change the text of a block
   * @param {Number} index the index of the block to change
   * @param {String} newText the new text of the block
   * @param {String} oldText the old text of the block
   */
  constructor(index, newText, oldText = null) {
    this.index = index;
    this.newText = newText;
    this.oldText = oldText;
  }

  /**
   * Executes the command on the given notebook
   * @param {Notebook} notebook the notebook to execute the command on
   */
  execute(notebook) {
    this.oldText = notebook.blocks[this.index].text;
    notebook.blocks[this.index].text = this.newText;
  }

  /**
   * @return {InputCommand} the command that does the opposite of `this`
   */
  reverse() {
    return new InputCommand(this.index, this.oldText, this.newText);
  }
}

/**
 * A command to add blocks to a notebook
 */
class AddBlocksCommand {
  /**
   * Creates a new command to insert blocks
   * @param {Number} index the index at which to insert blocks
   * @param {Array} blocks the blocks to insert
   */
  constructor(index, blocks) {
    this.index = index;
    this.blocks = blocks;
  }

  /**
   * Executes the command on the given notebook
   * @param {Notebook} notebook the notebook to execute the command on
   */
  execute(notebook) {
    const beforeNew = notebook.blocks.slice(0, this.index);
    const afterNew = notebook.blocks.slice(this.index);
    notebook.blocks = beforeNew
        .concat(this.blocks)
        .concat(afterNew);
  }

  /**
   * @return {AddBlocksCommand} the command that does the opposite of `this`
   */
  reverse() {
    return new RemoveBlocksCommand(this.index, this.blocks.length, this.blocks);
  }
}

/**
 * A command to remove blocks from the notebook
 */
class RemoveBlocksCommand {
  /**
   * Creates a new command to remove blocks
   * @param {Number} index the index at which to remove blocks
   * @param {Number} count the number of blocks to remove
   * @param {Array} blocks the blocks that were deleted
   */
  constructor(index, count, blocks = null) {
    this.index = index;
    this.count = count;
    this.blocks = blocks;
  }

  /**
   * Executes the command on the given notebook
   * @param {Notebook} notebook the notebook to execute the command on
   */
  execute(notebook) {
    this.blocks = notebook.blocks.splice(this.index, this.count);
  }

  /**
   * @return {AddBlocksCommand} the command that does the opposite of `this`
   */
  reverse() {
    return new AddBlocksCommand(this.index, this.blocks.map(cloneBlock));
  }
}

/**
 * A command that contains multiple commands. This is used for complicated
 * 'atomic' actions such as inserting input start and end blocks.
 */
class CompoundCommand {
  /**
   * @param {Array} commands the array of commands to use
   */
  constructor(commands) {
    this.commands = commands;
  }

  /**
   * Executes all the containing commands on the given notebook
   * @param {Notebook} notebook the notebook to execute all the commands on
   */
  execute(notebook) {
    for (const command of this.commands) {
      command.execute(notebook);
    }
  }

  /**
   * @return {CompoundCommand} the reverse of this command. This involves
   * reversing all subcommands, and executing them in reverse order.
   */
  reverse() {
    const newList = this.commands.map((command) => command.reverse());
    return new CompoundCommand(
        newList.reverse(),
    );
  }
}

/**
 * Creates a shallow copy of a block, and resets the `status` field
 * @param {Object} block the block to clone
 * @return {Object} a shallow copy of `block`, with the `status` field reset
 */
function cloneBlock(block) {
  const obj = {};
  for (const key in block) {
    if (Object.prototype.hasOwnProperty.call(block, key)) {
      obj[key] = block[key];
    }
  }
  Notebook.setDefaultBlockState(block);
  return obj;
}

/**
 * @param {Command} cmd1 the first command
 * @param {Command} cmd2 the second command, which is not executed yet
 * @return {Boolean} true if the two passed commands should be considered as a
 *    single action.
 */
function canMerge(cmd1, cmd2) {
  if (cmd1 instanceof AddBlocksCommand && cmd2 instanceof InputCommand) {
    // If cmd1 adds an empty block that cmd2 then gives text, we merge them
    const {index, blocks} = cmd1;
    const newIndex = cmd2.index;
    if (index <= newIndex && newIndex < index + blocks.length) {
      const indexInBlocks = newIndex - index;
      if (blocks[indexInBlocks].text === '') {
        return true;
      }
    }
  }
  if (cmd1 instanceof InputCommand && cmd2 instanceof RemoveBlocksCommand) {
    // If cmd1 clears the text of a block that cmd2 then removes, we merge them
    const {index, count} = cmd2;
    const newIndex = cmd1.index;
    if (index <= newIndex && newIndex < index + count && cmd1.newText === '') {
      return true;
    }
  }

  return false;
}

/**
 * Returns the last step of a command. For 'atomic' commands, this is the entire
 * command, but for CompoundCommands it is the last atomic step.
 * @param {Command} cmd the command whose last step to find.
 * @return {Command} the last atomic step of `cmd`
 */
function lastStep(cmd) {
  if (cmd instanceof CompoundCommand) {
    return lastStep(cmd.commands[cmd.commands.length - 1]);
  } else {
    return cmd;
  }
}

export {
  UndoRedo,
  MAX_BUFFER_SIZE,
};
