const fs = require('fs');
const path = require('path');

const defaultConfigData = {sertopPath: ''};

/**
 * Read in the configuration file. The function looks for the file
 * in the folder specified by userPath. If it does not exist, it
 * tries to write default configuration data to the file.
 * @param {object} remote electron remote instance
 * @return {Promise<Object>} Promise with the configuration data
 */
function readConfiguration(remote) {
  return new Promise((resolve, reject) => {
    const userPath = remote.app.getPath('userData');
    const configPath = path.join(userPath, 'wpconfig.json');
    let configData = defaultConfigData;

    console.log(`Looking for configuration file at ${configPath}`);

    fs.readFile(configPath, (err, data) => {
      if (err && (err['code'] === 'ENOENT')) {
        console.log('No configuration file found');
        // Write default configuration file
        fs.writeFile(configPath,
            JSON.stringify(configData, null, 4),
            (error) => {
              console.error('Could not create new configuration file');
            });
      } else {
        try {
          configData = JSON.parse(data);
        } catch ( err ) {
          console.log('error when parsing json file:');
          console.log(err);
        }
      }

      resolve(configData);
    });
  });
}

export {readConfiguration, defaultConfigData};
