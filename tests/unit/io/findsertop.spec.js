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
    return (userPath === specialPath ||
      specialPath.startsWith(userPath));
  };
}

/**
 * Helper function to quickly build a fake electron remote
 * returning the provided userpath with the function
 * .app.getPath('userData');
 * @param {string} userPath the mock user path
 * @param {array} chosenSertopPaths array of paths a user has chosen
 * @param {boolean} acceptMessage whether to accept message boxes
 * @return {Object} mock electron remote instance
 */
function remoteGen( userPath, chosenSertopPaths, acceptMessage=true ) {
  return {
    app: {getPath: (query) => {
      if (query === 'userData') {
        return userPath;
      } else if (query === 'home') {
        return 'C:\\Users\\SomeUser\\';
      } else {
        throw new Error('getPath not provided with correct argument');
      }
    }},
    dialog: {
      showOpenDialogSync: function() {
        return chosenSertopPaths;
      },
      showMessageBoxSync: function() {
        return acceptMessage ? 0 : 1;
      },
    },
  };
}

const userName = 'SomeUser';
const sertopPath = `C:\\OCaml64\\home\\${userName}\\.opam` +
        '\\ocaml-variants.4.07.1+mingw64c\\bin\\sertop.exe';

describe('Finding sertop', () => {
  beforeEach(() => {
    sandbox.replace(console, 'log', sinon.fake());
    sandbox.replace(console, 'warn', sinon.fake());
    sandbox.replace(console, 'error', sinon.fake());
  });

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
      const userPath = 'C:\\Users\\SomeUser\\AppData\\Roaming\\waterproof\\';
      const path = sertopFinder.findSertop('win32',
          remoteGen(userPath, [], true));
      expect(path).to.equal(sertopPath);
      done();
    });

    it('should not use that version if user rejects', (done) => {
      const userPath = 'C:\\Users\\SomeUser\\AppData\\Roaming\\waterproof\\';
      const path = sertopFinder.findSertop('win32',
          remoteGen(userPath, [], false));
      expect(path).to.equal('');
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

    it('should return empty string if path does not ' +
       'end with \'sertop.exe\'', (done)=> {
      const sertopPath = 'C:\\Users\\UserSertop\\sercomp.exe';
      const userPath = 'C:\\Users\\UserSertop\\AppData\\Roaming\\waterproof\\';
      expect(sertopFinder.userHelpFindSertop(remoteGen(userPath, [sertopPath])))
          .to.equal('');
      done();
    });
  });
});
