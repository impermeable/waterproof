export default {
  state: {
    done: false,
    message: 'Loading configuration...',
  },
  mutations: {
    loadingDone(state) {
      state.done = true;
      state.message = 'Done.';
    },
    setLoadingMessage(state, message) {
      state.message = message;
    },
  },
  actions: {
    loadSerapi(store) {
      setTimeout(() => {
        store.commit('setLoadingMessage', 'check libraries');
        setTimeout(() => {
          store.commit('loadingDone');
        }, 2500);
      }, 2500);
    },
  },
};
