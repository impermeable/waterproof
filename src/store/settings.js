export default {
  state: {
    settings: {
      scrollOnExec: false,
    },
  },
  mutations: {
    replaceSetting(state, setting) {
      state.settings[setting.name] = setting.value;
    },
  },
  actions: {
    setUserSetting(store, setting) {
      store.commit('replaceSetting', setting);
    },
  },
};
