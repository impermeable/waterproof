import fs from 'fs';

const path = require('path');
const util = require('util');
const execFile = util.promisify(require('child_process').execFile);
import {getAppdataPath, getResourcesPath} from './pathHelper';
import read, {deleteFile, doesFileExist, readFile} from './readfile';
import {blockToCoqText} from './notebook';

const extensions = ['wpn', 'v', 'vo'];

/**
 * Class that helps in building .vo files from .v files, using
 * a sercomp compiler.
 */
class VOCompiler {
  /**
   * Create a new VOCompiler, using the sercomp compiler
   * at the provided path
   * @param {string} sercompPath the path to sercomp
   * @param {Boolean} forceUpdates whether to re-compile forcibly
   */
  constructor(sercompPath, forceUpdates) {
    this.wrapperDirPath = getResourcesPath();
    this.sourcePath = path.join(this.wrapperDirPath, './wplib');
    this.wpLibPath = path.join(getAppdataPath(), './wplib');
    this.sercompPath = path.join(sercompPath);
    this.forceUpdates = forceUpdates;
  }

  /**
   * Check the library status and recompile if needed
   * @param {String} library
   * @return {Promise<void>}
   */
  async compileLibrary(library) {
    const currentFiles =
        await this.getFileExistance(path.join(this.wpLibPath, library));

    const libDirName = path.dirname(path.join(this.wpLibPath, library));

    if (!fs.existsSync(this.wpLibPath)) {
      fs.mkdirSync(this.wpLibPath);
    }

    if (!fs.existsSync(libDirName)) {
      fs.mkdirSync(libDirName);
    }

    if (this.forceUpdates) {
      if (currentFiles.vo) {
        await deleteFile(path.join(this.wpLibPath, library + '.vo'));
        currentFiles.vo = false;
      }
      if (currentFiles.v) {
        await deleteFile(path.join(this.wpLibPath, library + '.v'));
        currentFiles.v = false;
      }
      if (currentFiles.wpn) {
        await deleteFile(path.join(this.wpLibPath, library + '.wpn'));
        currentFiles.wpn = false;
      }
    }

    if (!currentFiles.wpn) {
      fs.copyFileSync(path.join(this.sourcePath, library + '.wpn'),
          path.join(this.wpLibPath, library + '.wpn'));
      currentFiles.wpn = true;
    }

    if (!currentFiles.v) {
      await this.notebookToCoq(path.join(this.wpLibPath, library + '.wpn'));
      currentFiles.v = true;
    }

    if (!currentFiles.vo) {
      await this.compileFile(path.join(this.wpLibPath, library + '.v'));
      currentFiles.vo = true;
    }
  }

  /**
   * Check which files (based on extensions) exist
   * @param {String} basePath the base path of the file
   * @return {Promise<void>} the resulting map with extensions
   */
  async getFileExistance(basePath) {
    const result = {};
    for (const extension of extensions) {
      result[extension] =
          await doesFileExist(basePath + '.' + extension);
    }
    return result;
  }

  /**
   * Convert notebook to v file for compilation
   * @param {String} filepath the path of the file to convert
   * @return {Promise<void>} promise which resolves when .v file is ready for
   *   compilation
   */
  async notebookToCoq(filepath) {
    if (!filepath.endsWith('.wpn')) {
      console.log('non notebook cant convert');
      return;
    }
    const notebook = await readFile(filepath);
    const text = blockToCoqText(notebook.blocks);

    return new Promise((resolve, reject) => {
      fs.writeFile(filepath.substring(0, filepath.length - 3) + 'v', text,
          (err) => {
            if (err) {
              reject(err);
            } else {
              resolve();
            }
          });
    });
  }

  /**
   * Compile a single file.
   * @param {string} filePath the path to the file to compile
   * @return {Promise} A promise with stdout and stderr of the compilation
   * process.
   */
  compileFile(filePath) {
    return execFile(this.sercompPath,
        ['--load-path=wplib,wplib',
          '--mode=vo',
          filePath],
        {cwd: getAppdataPath()});
  }
}

/**
 * Read the compile list file
 * @param {String} filePath the location of the file
 * @return {Promise<[]>} a promise which resolves into the list of files
 */
function getCompileList(filePath='') {
  if (!filePath) {
    filePath = path.join(getResourcesPath(), './wplib/compileList.json');
  }
  return new Promise((resolve, reject) => {
    const error = read(filePath, (list) => {
      resolve(list);
    });
    if (error != null) {
      reject(error);
    }
  });
}

export {VOCompiler, getCompileList};
