const fs = require('fs');
const path = require('path');
const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

import {updateConfiguration}
  from '../../../src/io/writeconfiguration.js';

// example configuration file contents
const configUserSertop =
    JSON.stringify({'sertopPath': 'C:\\Users\\Sertop\\sertop.exe'});
const configUserEmptySertop = JSON.stringify({'sertopPath': ''});
const configUserNoSertop = JSON.stringify({'irrelevantProps': ''});


const configFileName = 'wpconfig.json';

// dictionary to be used by the mock file system
const mockFiles = {
  [path.join('C:\\Users\\Sertop\\AppData\\Roaming\\waterproof\\',
      configFileName)]:
  configUserSertop,
  [path.join('C:\\Users\\EmptySertop\\AppData\\Roaming\\waterproof\\',
      configFileName)]:
  configUserEmptySertop,
  [path.join('C:\\Users\\NoSertop\\AppData\\Roaming\\waterproof\\',
      configFileName)]:
  configUserNoSertop,
};

// Replace the writeFile instance
// const writeFileStub = sinon.stub(fs, 'writeFile');

/**
 * Function to replace the fs.readFile function
 * @param {string} path the path to look for the file
 * @param {function} callback the callback function, taking in an error
 * argument and a data argument
 */
function readFileReplacement( path, callback ) {
  let err = null;
  let data = null;
  if ( !( path in mockFiles) ) {
    err = {code: 'ENOENT'};
  } else {
    data = mockFiles[path];
  }
  callback(err, data);
}

/**
 * Helper function to quickly build a fake electron remote
 * returning the provided userpath with the function
 * .app.getPath('userData');
 * @param {string} userPath the mock user path
 * @return {Object} mock electron remote instance
 */
function remoteGen( userPath ) {
  return {
    app: {getPath: (query) => {
      if (query === 'userData') {
        return userPath;
      } else {
        throw new Error('getPath not provided with correct argument');
      }
    }},
  };
}

const fileWriterStub = sinon.stub().yields(null);

describe('Updating the configuration file', () => {
  beforeEach(() => {
    sandbox.replace(fs, 'readFile', readFileReplacement);
    sandbox.replace(fs, 'writeFile', fileWriterStub);
    sandbox.replace(console, 'log', sinon.fake());
    sandbox.replace(console, 'warn', sinon.fake());
    sandbox.replace(console, 'error', sinon.fake());
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should write correct data to config file', (done)=> {
    const mySertopPath = 'C:\\Users\\Sertop\\sertop.exe';
    const userPath = 'C:\\Users\\Sertop\\AppData\\Roaming\\waterproof\\';
    updateConfiguration(remoteGen(userPath), {sertopPath: mySertopPath}).then(
        () => {
          expect(fileWriterStub.getCall(0).args[1]).to.deep.equal(
              JSON.stringify({sertopPath: mySertopPath}, null, 4));
          done();
        })
        .catch((err) => {
          done(err);
        });
  });

  it('should add sertopPath to configuration file if it was not there',
      (done) => {
        const mySertopPath = 'C:\\Users\\NoSertop\\sertop.exe';
        const userPath =
            'C:\\Users\\NoSertop\\AppData\\Roaming\\waterproof\\';
        updateConfiguration(remoteGen(userPath),
            {
              sertopPath: mySertopPath}).then(
            () => {
              expect(fileWriterStub.getCall(1).args[1]).to.deep.equal(
                  JSON.stringify({irrelevantProps: '',
                    sertopPath: mySertopPath}, null, 4));
              done();
            })
            .catch((err) => {
              done(err);
            });
      });
});
