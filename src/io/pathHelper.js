const path = require('path');

/**
 * Get a path to the resources folder.
 * @return {string} the path to the resources folder
 */
function getResourcesPath() {
  let resourcesPath;
  if (process.env.NODE_ENV === 'production') {
    resourcesPath = path.join(__dirname, '../../wrapper/');
  } else {
    resourcesPath = path.join('./wrapper/');
  }
  return path.resolve(resourcesPath);
}

/**
 * Get a path where we can (should be able to) store files
 * @return {string} the path
 */
function getAppdataPath() {
  if (process.env.NODE_ENV === 'test') {
    return 'C:\\Users\\Sertop\\AppData\\Roaming\\waterproof\\';
  }
  const electron = require('electron');
  // userdata just gives the appdata with a folder with waterproof
  return (electron.app || electron.remote.app).getPath('userData');
}

/**
 * Get the path to the log files directory
 * @return {string} the path to the log files directory
 */
function getLogfilesPath() {
  const basePath = getAppdataPath();
  return path.join(basePath, 'activity-logs');
}

export {getResourcesPath, getAppdataPath, getLogfilesPath};
