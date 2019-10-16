const path = require('path');

/**
 * This class covers finding paths to relevant folders.
 */
class PathHelper {
  /**
   * Get a path to the resources folder.
   * @return {string} the path to the resources folder
   */
  getResourcesPath() {
    let resourcesPath;
    if (process.env.NODE_ENV === 'production') {
      resourcesPath = path.join(__dirname, '../../wrapper/');
    } else {
      resourcesPath = path.join('./wrapper/');
    }
    return resourcesPath;
  }
}

export default PathHelper;
