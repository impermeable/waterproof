'use strict';

/* global __static */

import {getLogfilesPath} from './io/pathHelper';
import {app, BrowserWindow, ipcMain, protocol} from 'electron';
import {execFile} from 'child_process';
import path from 'path';
import fs from 'fs';
import {
  createProtocol,
} from 'vue-cli-plugin-electron-builder/lib';

const isDevelopment = process.env.NODE_ENV !== 'production';

// Keep a global reference of the window object, if you don't, the window will
// be closed automatically when the JavaScript object is garbage collected.
let win;
let wrapper;
let running = true;

// Scheme must be registered before the app is ready
protocol.registerSchemesAsPrivileged([
  {scheme: 'app', privileges: {secure: true, standard: true}},
]);

let wrapperPort = -1;
const wrapperPortWaiters = [];

/**
 * Set port
 * @param {Number} val the port
 */
function setPort(val) {
  if (wrapperPort >= 0) {
    console.log('WARNING ALREADY HAVE PORT', wrapperPort);
    return;
  }

  wrapperPort = val;
  wrapperPortWaiters.forEach((fn) => fn(wrapperPort));
}

/**
 * Creates Waterproof's main window.
 */
function createWindow() {
  // Create the browser window.

  let relPath;
  if (process.env.NODE_ENV === 'production') {
    relPath = '../../';
  } else {
    relPath = '../';
  }
  const basePath = path.join(__dirname, relPath);

  let wrapperExecutable = '';
  if (process.platform === 'win32') {
    wrapperExecutable = 'win/wpwrapper.exe';
  } else if (process.platform === 'darwin') {
    wrapperExecutable = 'mac/wpwrapper_mac.mac';
  } else {
    wrapperExecutable = 'lin/wpwrapper_ubuntu.ubuntu';
  }

  const wrapperPath = path.join(basePath, 'wrapper/' + wrapperExecutable);

  wrapper = execFile(wrapperPath, {cwd: app.getPath('home')},
      (error, stdout, stderr) => {
        if (running && error && error.signal !== 'SIGTERM') {
          console.log('Could not start wrapper');
          console.log(error);
        }
      });

  const portListener = (chunk) => {
    const lines = chunk.replaceAll('\r', '')
        .split('\n')
        .filter((l) => l.includes('started listening on port '));
    if (lines.length === 0) {
      return;
    }

    const parts = lines[0].split('started listening on port ');
    if (parts.length === 2) {
      const number = parts[1].trim();
      const result = Number.parseInt(number);
      console.log('got serapi port', result);
      if (!Number.isNaN(result)) {
        setPort(result);
        wrapper.stdout.removeListener('data', portListener);
        return;
      }
    } else {
      console.log('did not find port in log', parts);
    }

    wrapper.stdout.removeListener('data', portListener);
    // fallback to default
    setPort(51613);
  };

  wrapper.stdout.addListener('data', portListener);
  setTimeout(() => {
    // In case we don't get a message assume we got the default but keep
    // listening in case we're just early.
    if (wrapperPort === -1) {
      setPort(51613);
      wrapper.stdout.removeListener('data', portListener);
    }
  }, 5000);

  win = new BrowserWindow({
    width: 800,
    height: 600,
    minHeight: 500,
    minWidth: 500,
    title: 'Waterproof',
    webPreferences: {
      nodeIntegration: true,
      enableRemoteModule: true,
    },
    icon: path.join(__static, 'icon.png'),
  });

  // Remove OS top bar
  // win.setMenu(null);
  win.setMenuBarVisibility(false);

  if (process.env.WEBPACK_DEV_SERVER_URL) {
    // Load the url of the dev server if in development mode
    win.webContents.loadURL(process.env.WEBPACK_DEV_SERVER_URL).then(() => {
      if (process.argv.includes('--shutdown-on-pageload')) {
        app.quit();
        wrapper.kill('SIGTERM');
      }
    });
    if (!process.env.IS_TEST) win.webContents.openDevTools();
  } else {
    createProtocol('app');
    // Load the index.html when not in development

    if (process.argv.length > 1) {
      // TODO check on different platforms
      win.loadURL('app://./index.html?location=' + encodeURIComponent(process.argv[1])).then(() => {
        if (process.argv.includes('--shutdown-on-pageload')) {
          app.quit();
        }
      });
    } else {
      win.loadURL('app://./index.html').then(() => {
        if (process.argv.includes('--shutdown-on-pageload')) {
          app.quit();
        }
      });
    }
  }

  win.on('closed', () => {
    win = null;
  });

  win.on('close', function(e) {
    onActivity({type: 'closing', running: running});
    writePendingActivities();
    if (running) {
      win.webContents.send('closing-application');
      e.preventDefault();
    } else {
      wrapper.kill('SIGTERM');
    }
  });

  ipcMain.on('confirmClosing', () => {
    running = false;
    app.quit();
  });

  ipcMain.handle('serapi-port', async (event) => {
    if (wrapperPort >= 0) {
      return wrapperPort;
    }
    return await new Promise((resolve) => {
      wrapperPortWaiters.push(resolve);
    });
  });
}

// Quit when all windows are closed.
app.on('window-all-closed', () => {
  // On macOS it is common for applications and their menu bar
  // to stay active until the user quits explicitly with Cmd + Q
  if (process.platform !== 'darwin') {
    app.quit();
  }
});

app.on('activate', () => {
  // On macOS it's common to re-create a window in the app when the
  // dock icon is clicked and there are no other windows open.
  if (win === null) {
    createWindow();
  }
});

// This method will be called when Electron has finished
// initialization and is ready to create browser windows.
// Some APIs can only be used after this event occurs.
app.on('ready', async () => {
  createWindow();
});

// Exit cleanly on request from parent process in development mode.
if (isDevelopment) {
  if (process.platform === 'win32') {
    process.on('message', (data) => {
      if (data === 'graceful-exit') {
        app.quit();
      }
    });
  } else {
    process.on('SIGTERM', () => {
      app.quit();
    });
  }
}

const pendingActivities = [];

function onActivity(activity) {
  const timeSinceStart = new Date - startTime;
  Object.assign(activity, {sinceBoot: timeSinceStart});
  pendingActivities.push(activity);
}

const startTime = (() => {
  const now = new Date;
  pendingActivities.push({type: 'boot', time: now, sinceBoot: 0});
  return +now;
})();

ipcMain.on('activity', (event, args) => {
  onActivity(args);
});

const activityFile = (() => {
  const basePath = getLogfilesPath();
  const fileName = 'activity-' +
      (+new Date).toString().padStart(12, '0') + '.log';
  fs.mkdirSync(basePath, {recursive: true});
  return path.join(basePath, fileName);
})();

const activityStream = fs.createWriteStream(activityFile, {
  flags: 'a', autoClose: true,
});

/**
 * Calculate a 32 bit FNV-1a hash
 * Found here: https://gist.github.com/vaiorabbit/5657561
 * Ref.: http://isthe.com/chongo/tech/comp/fnv/
 *
 * @param {string} str the input value
 * @param {integer} [seed] optionally pass the hash of the previous chunk
 * @return {string}
 */
function hashFnv32a(str) {
  // This comes from https://stackoverflow.com/a/22429679
  let hval = 0x5BC230F9;
  const l = str.length;
  for (let i = 0; i < l; i++) {
    hval ^= str.charCodeAt(i);
    hval += (hval << 1) + (hval << 4) +
        (hval << 7) + (hval << 8) + (hval << 24);
  }

  return (hval >>> 0).toString(16).padStart(8, '0');
}

function anonymizePath(pathAsString) {
  if (pathAsString == null) {
    return null;
  }
  try {
    const pathObject = path.parse(pathAsString);
    const dirHash = hashFnv32a(pathObject.dir);
    return dirHash + '-' + pathObject.base;
  } catch (e) {
    return null;
  }
}

function preProcessActivity(activity) {
  if ('file' in activity) {
    activity.file = anonymizePath(activity.file);
  } else if ('location' in activity) {
    activity.location = anonymizePath(activity.location);
  }
  return activity;
}

function writePendingActivities() {
  if (process.env.NODE_ENV === 'test') {
    console.log('Skipping activity log writing because of testing');
    console.log('Would have written', pendingActivities);
    pendingActivities.length = 0;
    return;
  }
  pendingActivities.forEach((act) => {
    act = preProcessActivity(act);
    activityStream.write(JSON.stringify(act) + '\n');
  });
  pendingActivities.length = 0;
}

const logWriteTime = process.env.NODE_ENV === 'development' ? 3000 : 30000;
setInterval(() => {
  if (pendingActivities.length === 0) {
    onActivity({type: 'heartbeat'});
  }
  writePendingActivities();
}, logWriteTime);
