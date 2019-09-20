const fs = require('fs');

/**
 * Function for reading a json file
 * @param {String} file the file to read
 * @param {Function} onSuccess called when file is loaded
 */
function read(file, onSuccess) {
  fs.readFile(file, (err, data) => {
    if (err) {
      console.error(err);
      return;
    }

    let assistanceItemList;
    try {
      assistanceItemList = JSON.parse(data);
    } catch (error) {
      console.error(error);
      return;
    }

    onSuccess(assistanceItemList);
  });
}

export default read;
