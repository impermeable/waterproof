const fs = require('fs');
const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

import {readConfiguration, defaultConfigData}
  from '../../../src/io/readconfiguration.js';

// example configuration file contents
const configUserSertop =
    JSON.stringify({'sertopPath': 'C:\\Users\\UserSertop\\sertop.exe'});
const configUserEmptySertop = JSON.stringify({'sertopPath': ''});
const configUserNoSertop = JSON.stringify({'irrelevantProps': ''});
const configUserBadJSON = '{ not : valid : json }';

// dictionary to be used by the mock file system
const mockFiles = {
  'C:\\Users\\UserSertop\\AppData\\Roaming\\waterproof\\wpconfig.json':
    configUserSertop,
  'C:\\Users\\UserEmptySertop\\AppData\\Roaming\\waterproof\\wpconfig.json':
    configUserEmptySertop,
  'C:\\Users\\UserNoSertop\\AppData\\Roaming\\waterproof\\wpconfig.json':
    configUserNoSertop,
  'C:\\Users\\UserBadJSON\\AppData\\Roaming\\waterproof\\wpconfig.json':
    configUserBadJSON,
};

// Replace the writeFile instance
sinon.stub(fs, 'writeFile');

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

describe('Reading the configuration file', () => {
  beforeEach(() => {
    sandbox.replace(fs, 'readFile', readFileReplacement);
  });

  afterEach(() => {
    sandbox.restore();
  });

  it('should return correct sertopPath if it is in config file', (done)=> {
    const sertopPath = 'C:\\Users\\UserSertop\\sertop.exe';
    const userPath = 'C:\\Users\\UserSertop\\AppData\\Roaming\\waterproof\\';
    readConfiguration(remoteGen(userPath)).then(
        (result) => {
          expect(result['sertopPath']).to.equal(sertopPath);
          done();
        })
        .catch((err) => {
          done(err);
        });
  });

  it('should return empty path if sertopPath empty in config file', (done)=> {
    const sertopPath = '';
    const userPath =
        'C:\\Users\\UserEmptySertop\\AppData\\Roaming\\waterproof\\';
    readConfiguration(remoteGen(userPath)).then(
        (result) => {
          expect(result['sertopPath']).to.equal(sertopPath);
          done();
        })
        .catch((err) => {
          done(err);
        });
  });

  it('should return read configData if sertopPath not in config file',
      (done) => {
        const userPath =
            'C:\\Users\\UserNoSertop\\AppData\\Roaming\\waterproof\\';
        readConfiguration(remoteGen(userPath)).then(
            (result) => {
              expect(result).to.deep.equal({'irrelevantProps': ''});
              done();
            })
            .catch((err) => {
              done(err);
            });
      });

  it('should return default configData if JSON cannot be parsed', (done)=> {
    const userPath =
        'C:\\Users\\UserBadJSON\\AppData\\Roaming\\waterproof\\';
    readConfiguration(remoteGen(userPath)).then(
        (result) => {
          expect(result).to.equal(defaultConfigData);
          done();
        })
        .catch((err) => {
          done(err);
        });
  });

  it('should return empty path if not in config file', (done) => {
    const sertopPath = '';
    const userPath = 'C:\\Users\\UserNoConfig\\AppData\\Roaming\\waterproof\\';
    readConfiguration(remoteGen(userPath)).then(
        (result) => {
          expect(result['sertopPath']).to.equal(sertopPath);
          done();
        })
        .catch((err) => {
          done(err);
        });
  });
});
