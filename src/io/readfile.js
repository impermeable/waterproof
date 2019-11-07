const fs = require('fs');

/**
 * Function for reading a json file
 * @param {String} file the file to read
 * @param {Function} onSuccess called when file is loaded
 * @return {Undefined|Error} returns undefined on success and an error if one
 *  occurred
 */
function read(file, onSuccess) {
  let occurredError = undefined;
  fs.readFile(file, (err, data) => {
    if (err) {
      console.error(err);
      occurredError = err;
      return;
    }

    let assistanceItemList;
    try {
      assistanceItemList = JSON.parse(data);
    } catch (error) {
      console.error(error);
      occurredError = err;
      return;
    }

    onSuccess(assistanceItemList);
  });
  return occurredError;
}

export default read;

/**
 * Check if the file exists
 * @param {String} filepath the path of the file to check
 * @return {Promise<Boolean>} promise which resolves to true if the file exists
 */
function doesFileExist(filepath) {
  return new Promise(((resolve) => {
    fs.access(filepath, fs.constants.F_OK, (err) => {
      if (err) {
        resolve(false);
      } else {
        resolve(true);
      }
    });
  }));
}

/**
 * Remove a file
 * @param {String} filepath the path of the file to remove
 * @return {Promise<Boolean>} returns true if file removed
 *   (rejects if any error)
 */
function deleteFile(filepath) {
  return new Promise((resolve, reject) => {
    fs.unlink(filepath, (err) => {
      if (err) {
        reject(err);
      } else {
        resolve();
      }
    });
  });
}

/**
 * Read a file with promise
 * @param {String} filepath the path of the file to read
 * @return {Promise<unknown>}
 */
function readFile(filepath) {
  return new Promise(((resolve, reject) => {
    fs.readFile(filepath, (err, data) => {
      if (err) {
        console.error(err);
        reject(err);
        return;
      }

      let parsedData;
      try {
        parsedData = JSON.parse(data);
      } catch (error) {
        console.error(error);
        reject(err);
        return;
      }

      resolve(parsedData);
    });
  }));
}

export {doesFileExist, deleteFile, readFile};
