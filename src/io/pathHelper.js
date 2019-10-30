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

export {getResourcesPath};
