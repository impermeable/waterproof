'use strict';

/* global __static */

import {app, BrowserWindow, ipcMain, protocol} from 'electron';
import {execFile} from 'child_process';
import path from 'path';
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
      (error) => {
        if (running && error && error.signal !== 'SIGTERM') {
          console.log('Could not start wrapper');
          console.log(error);
        }
      });

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
