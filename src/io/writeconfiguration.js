const fs = require('fs');
const path = require('path');
import {readConfiguration} from './readconfiguration';

const defaultConfigData = {sertopPath: ''};
const possibleKeys = ['sertopPath'];


/**
 * Update the configuration file. The function looks for the file
 * in the folder specified by userPath.
 * @param {object} remote electron remote instance
 * @param {object} variablesToUpdate an object with variables that should
 * be updated in the configuration file, for instance
 * {sertopPath: 'C:\sertop.exe'}
 * @return {Promise<Object>} Promise to allow for waiting
 * for the function to complete
 */
function updateConfiguration(remote, variablesToUpdate) {
  return new Promise((resolve, reject) => {
    const userPath = remote.app.getPath('userData');
    const configPath = path.join(userPath, 'wpconfig.json');
    let configData = defaultConfigData;

    readConfiguration(remote).then((result) => {
      configData = result;
      for (const key in variablesToUpdate) {
        if ( possibleKeys.includes(key) ) {
          configData[key] = variablesToUpdate[key];
        }
      }
      fs.writeFile(configPath,
          JSON.stringify(configData, null, 4),
          (error) => {
            if (error) {
              console.error('Could not write to configuration file');
              reject(error);
            } else {
              resolve();
            }
          });
    }).catch((err) => {
      console.log('Error when reading configuration file prior to updating');
      reject(err);
    });
  });
}

export {updateConfiguration};
