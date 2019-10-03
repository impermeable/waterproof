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
    * @return {string} The path of sertop if it is found,
    * and otherwise an empty string.
    */
function findSertop(platform) {
  const userName = os.userInfo()['username'];
  if (platform === 'win32') {
    const ocamlVariants =
        ['default',
          'ocaml-variants.4.07.1+mingw64c',
          '4.07.1+mingw64c'];
    for (let i=0; i < ocamlVariants.length; i++ ) {
      const guess = `C:\\OCaml64\\home\\${userName}\\.opam` +
            `\\${ocamlVariants[i]}\\bin\\sertop.exe`;
      if (fs.existsSync(guess)) {
        return guess;
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
  const result = remote.dialog.showOpenDialog({
    title: 'Please select sertop',
    defaultPath: guess,
    properties: ['openFile']});
  if (result) {
    return result[0];
  } else {
    const userPath = remote.app.getPath('userData');
    const configPath = path.join(userPath, 'wpconfig.json');
    console.warn('Please specify a path for sertop ' +
         `in the configuration file ${configPath}`);
  }
  return '';
}

export {findSertop, userHelpFindSertop, getPlatform};
