const fs = require('fs');
const path = require('path');

const defaultConfigData = {
  sertopPath: '',
  serapiVersion: '',
};
const possibleKeys = ['sertopPath', 'serapiVersion'];

/**
 * Read in the configuration file. The function looks for the file
 * in the folder specified by userPath. If it does not exist, it
 * tries to write default configuration data to the file.
 * @param {object} remote electron remote instance
 * @return {Promise<Object>} Promise with the configuration data
 */
function readConfiguration(remote) {
  return new Promise((resolve) => {
    const userPath = remote.app.getPath('userData');
    const configPath = path.join(userPath, 'wpconfig.json');
    let configData = defaultConfigData;

    console.log(`Looking for configuration file at ${configPath}`);

    fs.readFile(configPath, (err, data) => {
      console.log('Read config file:', String(data), ' error: ', err);
      if (err && (err['code'] === 'ENOENT')) {
        console.log('No configuration file found');
        // Write default configuration file
        fs.writeFile(configPath,
            JSON.stringify(configData, null, 4),
            () => {
              console.error('Could not create new configuration file');
            });
        console.log('(Tried to) Write configuration file');
      } else {
        try {
          configData = JSON.parse(String(data));
          console.log('Read configuration file');
        } catch ( err ) {
          console.log('error when parsing json file:');
          console.log(err);
        }
      }

      resolve(configData);
    });
  });
}

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

export {readConfiguration, defaultConfigData, updateConfiguration};
