const fs = require('fs');
const os = require('os');

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

const sertopFinder = require('../../../src/io/findsertop');

/**
 * Returns a replacement for the filesystem's 'existsSync' function.
 * @param {string} specialPath The replacement will return true
 * if provided with the 'specialPath', and otherwise it will return false.
 * @return {boolean} true if provided with 'specialPath', false otherwise
 */
function existsSyncReplacement( specialPath ) {
  return function(userPath) {
    if (userPath === specialPath) {
      return true;
    }
    return false;
  };
}

/**
 * Helper function to quickly build a fake electron remote
 * returning the provided userpath with the function
 * .app.getPath('userData');
 * @param {string} userPath the mock user path
 * @param {array} chosenSertopPaths array of paths a user has chosen
 * @return {Object} mock electron remote instance
 */
function remoteGen( userPath, chosenSertopPaths ) {
  return {
    app: {getPath: (query) => {
      if (query === 'userData') {
        return userPath;
      } else {
        throw new Error('getPath not provided with correct argument');
      }
    }},
    dialog: {showOpenDialog: function() {
      return chosenSertopPaths;
    },
    },
  };
}

const userName = 'SomeUser';
const sertopPath = `C:\\OCaml64\\home\\${userName}\\.opam` +
        '\\ocaml-variants.4.07.1+mingw64c\\bin\\sertop.exe';

describe('Finding sertop', () => {
  afterEach(() => {
    sandbox.restore();
  });

  describe('Finding sertop on Windows', () => {
    beforeEach( () => {
      sandbox.replace(os, 'userInfo', sinon.stub().
          returns({username: 'SomeUser'}));
      sandbox.replace(fs, 'existsSync', existsSyncReplacement(sertopPath));
    });

    it('should give back correct path on Windows', (done) => {
      expect(sertopFinder.findSertop('win32')).to.equal(sertopPath);
      done();
    });
  });

  describe('Finding sertop with help of the user', () => {
    it('should return correct sertopPath ' +
       'if it is selected by the user', (done)=> {
      const sertopPath = 'C:\\Users\\UserSertop\\sertop.exe';
      const userPath = 'C:\\Users\\UserSertop\\AppData\\Roaming\\waterproof\\';
      expect(sertopFinder.userHelpFindSertop(remoteGen(userPath, [sertopPath])))
          .to.equal(sertopPath);
      done();
    });
  });
});
