import {findSertop, userHelpFindSertop} from '../io/findsertop';
import {updateConfiguration} from '../io/configurationio';
import {remote} from 'electron';
import {getCompileList, VOCompiler} from '../io/compileToVO';
import {doesFileExist} from '../io/readfile';
const util = require('util');
const execFile = util.promisify(require('child_process').execFile);

export default {
  state: {
    done: false,
    message: 'Loading configuration...',
    sertopPath: null,
    sercompPath: null,
    serapiVersion: null,
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
      state.sertopPath = result['sertopPath'];
      state.serapiVersion = result['serapiVersion'];
    },
    setSercompPath(state, path) {
      state.sercompPath = path;
    },
    updateConfig(state, partial) {
      if (partial.hasOwnProperty('sertopPath')) {
        state.sertopPath = partial['sertopPath'];
      }
      if (partial.hasOwnProperty('serapiVersion')) {
        state.sertopPath = partial['serapiVersion'];
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
      store.dispatch('readConfig').then(async () => {
        store.commit('setLoadingMessage', 'Reading serapi location');
        if (store.state.sertopPath === '' || store.state.sertopPath == null) {
          const result = await userHelpFindSertop(remote,
              findSertop(process.platform));
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
        console.log('should have valid sercomp path:', store.state.sercompPath);

        if (store.state.sertopPath === '' || store.state.sertopPath == null) {
          store.commit('setLoadingMessage', 'Could not find serapi');
          return;
        }
        store.commit('setLoadingMessage', 'Getting serapi version');

        const newVersion = await store.dispatch('getSerapiVersion');

        store.commit('setLoadingMessage', 'Reading library list');

        await store.dispatch('compileLibraries', newVersion);
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
              `Updating/Compiling libraries (${libDone + 1} / ${libTotal})`
              + ` ${library}`);
        }
        await compiler.compileLibrary(library);
        libDone++;
      }

      store.commit('loadingDone');
    },
  },
};
