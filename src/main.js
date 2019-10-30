import Vue from 'vue';
import App from './App.vue';
import store from './store/store';
import BootstrapVue from 'bootstrap-vue';

// add the coq mode to codemirror
import '../codemirror/CoqCodemirrorMode';

import VueRouter from 'vue-router';
import routes from './router';


Vue.config.productionTip = false;
Vue.use(require('vue-shortkey'));
Vue.use(Vuex);
Vue.use(BootstrapVue);
Vue.use(VueRouter);

// We import this here (instead of via style-resources-loader) to prevent
// duplication.
import './assets/stylesheets/_common.scss';


import '../assets/sass/main.scss';

new Vue({
  store,
  router: new VueRouter(routes),
  render: (h) => h(App),
}).$mount('#app');
