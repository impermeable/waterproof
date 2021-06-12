import {findSertop, userHelpFindSertop} from '../io/findsertop';
import {updateConfiguration} from '../io/configurationio';
import {remote} from 'electron';
import {getCompileList, VOCompiler} from '../io/compileToVO';
import {doesFileExist} from '../io/readfile';
import TCPManager from '../coq/serapi/workers/TCPManager';
import {Mutex} from 'async-mutex';
import CoqSerapiProcessors from '../coq/serapi/processors/CoqSerapiProcessors';
const util = require('util');
const execFile = util.promisify(require('child_process').execFile);

export default {
  state: {
    done: false,
    message: 'Loading configuration...',
    lock: new Mutex,
    sertopPath: null,
    sercompPath: null,
    serapiVersion: null,
    libraryVersion: null,
    socket: new TCPManager(),
  },
  mutations: {
    loadingDone(state) {
      state.done = true;
      state.message = 'Done.';
    },
    setLoadingMessage(state, message) {
      state.done = false;
      state.message = message;
    },
    setConfig(state, result) {
      console.log('Setting config ', JSON.parse(JSON.stringify(result)));
      state.sertopPath = result['sertopPath'];
      state.serapiVersion = result['serapiVersion'];
      state.libraryVersion = result['libraryVersion'];
    },
    setSercompPath(state, path) {
      state.sercompPath = path;
    },
    updateConfig(state, partial) {
      if (Object.prototype.hasOwnProperty.call(partial, 'sertopPath')) {
        state.sertopPath = partial['sertopPath'];
      }
      if (Object.prototype.hasOwnProperty.call(partial, 'serapiVersion')) {
        state.serapiVersion = partial['serapiVersion'];
      }
      if (Object.prototype.hasOwnProperty.call(partial, 'libraryVersion')) {
        state.libraryVersion = partial['libraryVersion'];
      }
    },
  },
  actions: {
    getSertopPath: function({commit, dispatch, state}) {
      return new Promise((resolve, reject) => {
        if (state.configLoaded) {
          resolve(state.sertopPath);
        } else {
          dispatch('readConfig').then(() => {
            if (state.sertopPath === '') {
              const result = userHelpFindSertop(remote,
                  findSertop(process.platform));
              console.log(`user selected sertop at: ${result}`);
              if (result) {
                updateConfiguration(remote,
                    {sertopPath: result}).then(() => {
                  commit('setConfig', {sertopPath: result});
                  resolve(result);
                }).catch((err) => {
                  console.log(err);
                  reject(err);
                });
              } else {
                resolve('');
              }
            } else {
              resolve(state.sertopPath);
            }
          }, (reason) => {
            reject( reason );
          } );
        }
      });
    },
    updateLibraries: async function(store) {
      const release = await store.state.lock.acquire();

      store.commit('setLoadingMessage', 'Getting serapi version');
      const newVersion = await store.dispatch('getSerapiVersion');

      store.commit('setLoadingMessage', 'Getting library version');
      const appVersion = require('electron').remote.app.getVersion();
      const libVersion = store.state.libraryVersion;

      // If serapi has updated or waterproof itself -> force recompile
      const forceRecompile = appVersion !== libVersion || newVersion;

      store.commit('setLoadingMessage', 'Reading library list');
      await store.dispatch('compileLibraries', forceRecompile);

      release();
    },
    resolveSercompPath: async function(store) {
      if (store.state.sertopPath == null || store.state.sertopPath === '') {
        return;
      }

      // TODO make sure to only replace the last one
      const sercompPath = store.state.sertopPath.replace('sertop', 'sercomp');

      return new Promise(((resolve, reject) => {
        const exists = doesFileExist(sercompPath);
        if (!exists) {
          reject(new Error('sercomp does not exist'));
        } else {
          store.commit('setSercompPath', sercompPath);
          resolve(sercompPath);
        }
      }));
    },
    async loadSerapi(store) {
      const release = await store.state.lock.acquire();
      if (store.state.done) {
        console.log('Already loaded serapi');
        release();
        return;
      }
      console.log('Loading serapi...');
      store.dispatch('readConfig').then(async () => {
        console.log('readConfig');
        store.commit('setLoadingMessage', 'Reading serapi location');
        if (store.state.sertopPath === '' || store.state.sertopPath == null) {
          let result = findSertop(process.platform);
          if (result === '') {
            result = await userHelpFindSertop(remote,
                result);
          }
          console.log(`user selected sertop at: ${result}`);

          if (result) {
            try {
              await updateConfiguration(remote, {sertopPath: result});
              store.commit('updateConfig', {sertopPath: result});
            } catch (e) {
              console.log(e);
            }
          }
        }

        await store.dispatch('resolveSercompPath');

        if (store.state.sertopPath === '' || store.state.sertopPath == null) {
          store.commit('setLoadingMessage', 'Could not find serapi');
          return;
        }
        release();
        store.dispatch('updateLibraries');
      });
    },
    async getSerapiVersion(store) {
      if (store.state.sertopPath == null || store.state.sertopPath === '') {
        return;
      }
      return execFile(store.state.sertopPath, ['--version'])
          .then(async (result) => {
            const versionString = result.stdout.trim();
            const isNewVersion = store.state.serapiVersion !== versionString;
            if (isNewVersion) {
              await updateConfiguration(remote, {serapiVersion: versionString});
              store.commit('updateConfig', {serapiVersion: versionString});
            }
            return isNewVersion;
          });
    },
    async compileLibraries(store, forced) {
      store.commit('setLoadingMessage', 'compiling libraries');
      const libFiles = await getCompileList();

      let libDone = 0;
      const libTotal = libFiles.length;

      const compiler = new VOCompiler(store.state.sercompPath, forced);

      for (const library of libFiles) {
        if (!store.state.done) {
          store.commit('setLoadingMessage',
              `Compiling libraries ${libDone + 1}/${libTotal}` +
               ` (${library})`);
        }
        await compiler.compileLibrary(library);
        libDone++;
      }

      // Also store the version of Waterproof of this lib compilation
      const appVersion = require('electron').remote.app.getVersion();
      await updateConfiguration(remote, {libraryVersion: appVersion});
      store.commit('updateConfig', {libraryVersion: appVersion});

      store.commit('loadingDone');
    },
    async createCoqInstance(store, editorInterface) {
      await store.dispatch('loadSerapi');
      const worker = store.state.socket.createNewWorker(store.state.sertopPath);
      return new CoqSerapiProcessors(worker, editorInterface);
    },
    async shutdownSerapi(store) {
      await store.dispatch('loadSerapi');
      return new Promise((resolve) => {
        store.state.socket.stopAll(resolve);
      });
    },
  },
};
