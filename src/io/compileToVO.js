const path = require('path');

const util = require('util');
const execFile = util.promisify(require('child_process').execFile);
import PathHelper from './pathHelper';
import read from './readfile';

/**
 * Class that helps in building .vo files from .v files, using
 * a sercomp compiler.
 */
class VOCompiler {
  /**
   * Create a new VOCompiler, using the sercomp compiler
   * at the provided path
   * @param {string} sercompPath the path to sercomp
   */
  constructor(sercompPath) {
    const pathHelper = new PathHelper();
    this.wrapperDirPath = pathHelper.getResourcesPath();
    this.sercompPath = path.join(sercompPath);
  }

  /**
   * Compile a single file.
   * @param {string} filePath the path to the file to compile
   * @param {string} wrapperDirPath the path to the resources directory
   * @param {string} sercompPath the path to sercomp
   * @return {Promise} A promise with stdout and stderr of the compilation
   * process.
   */
  compileFile(filePath) {
    return execFile(this.sercompPath,
        ['--load-path=wplib,wplib',
          '--mode=vo',
          filePath],
        {cwd: this.wrapperDirPath});
  }

  /**
   * Compile a list of files.
   * @param {Array} filePaths an array with the paths of the files to compile
   */
  async compileFiles(filePaths) {
    for (let i = 0; i < filePaths.length; i++) {
      const filePath = path.join('./wplib', filePaths[i]);
      try {
        await this.compileFile(filePath);
      } catch (err) {
        console.log(err);
        throw err;
      }
    }
  }

  /**
   * Compile a list of files from a file describing
   * the order in which to compile.
   * @param {string} listFilePath the path to the file with the list. If empty,
   * a standard path is chosen.
   * @return {Promise} a promise that resolves when the files are processed.
   */
  compileFromListFile(listFilePath='') {
    return new Promise((resolve, reject) => {
      let filePath = listFilePath;
      if (filePath==='') {
        filePath = path.join(this.wrapperDirPath, './wplib/compileList.json');
      }
      read(filePath, (fileList) => {
        this.compileFiles(fileList).then((result) => {
          resolve();
        }).catch((err) => {
          console('error when compiling files:');
          console.log(err);
          reject(err);
        });
      });
    });
  }
}

export {VOCompiler};
