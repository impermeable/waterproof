import {getAppdataPath} from './pathHelper';

const fs = require('fs');
const os = require('os');
const path = require('path');

/**
 * Small wrapper to get the platform,
 * useful for testing purposes
 * @return {string} platform of the user
 */
function getPlatform() {
  return process.platform;
}

/**
  * Attempts to find the location of sertop.
  *
  * @param {string} platform the platform of the user
  * @param {Object} remote electron remote instance
  * @return {string} The path of sertop if it is found,
  * and otherwise an empty string.
  */
function findSertop(platform, remote=undefined) {
  if (remote == null) {
    // TODO: ugly for testing... can be done better
    remote = require('electron').remote;
  }
  const userName = os.userInfo()['username'];
  if (platform === 'win32') {
    const ocamlVariants =
        ['coq_for_waterproof',
          'default',
          'ocaml-variants.4.07.1+mingw64c',
          '4.07.1+mingw64c',
          '4.11.1+mingw64c'];

    const baseFolderVariants =
        ["C:\\cygwin_coq_platform\\home\\runneradmin\\.opam\\",
          `C:\\OCaml64\\home\\${userName}\\.opam\\`,
          path.join(remote.app.getPath('home'), '.opam/')];
    for (const base of baseFolderVariants) {
      if (fs.existsSync(base)) {
        for (const variant of ocamlVariants) {
          const guess = base + `${variant}\\bin\\sertop.exe`;
          if (fs.existsSync(guess)) {
            const dialog = remote.dialog;

            const useThisVersion =dialog.showMessageBoxSync({
              type: 'question',
              title: 'Found serapi version',
              message: `Waterproof makes use of a program called sertop.` +
                  ` Waterproof found a version of sertop at:\n${guess}\n` +
                  `Should waterproof use this version?\n` +
                  `(This can be changed later in the configuration file)`,
              buttons: [
                'Yes',
                'No',
              ],
            });

            if (useThisVersion === 0) {
              return guess;
            }
          }
        }
      }
    }
  }
  return '';
}

/**
 * Let the user select sertop, possibly based on a
 * guess on where to find it.
 * @param {Object} remote electron remote instance
 * @param {string} guess a guess where to find sertop.
 * Can be an empty string.
 * @return {Promise<string>} A promise which, when resolved,
 * gives back a string with the sertop Path
 */
function userHelpFindSertop(remote, guess='') {
  const userPath = getAppdataPath();
  const configPath = path.join(userPath, 'wpconfig.json');
  const result = remote.dialog.showOpenDialogSync({
    title: 'Please select the program named sertop',
    message: 'Please select the program named sertop',
    defaultPath: guess,
    FileFilter: {name: 'sertop', extensions: ['exe', '']},
    properties: ['openFile']});
  if (result) {
    if (result[0].endsWith('sertop.exe') || result[0].endsWith('sertop')) {
      return result[0];
    } else {
      console.warn('Please specify a valid path for sertop ' +
         `in the configuration file ${configPath}`);
      return '';
    }
  } else {
    console.warn('Please specify a path for sertop ' +
         `in the configuration file ${configPath}`);
  }
  return '';
}

export {findSertop, userHelpFindSertop, getPlatform};
