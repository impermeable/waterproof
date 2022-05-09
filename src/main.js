import Vue from 'vue';
import Vuex from 'vuex';
import App from './App.vue';
import BootstrapVue from 'bootstrap-vue';
import {writeActivity} from '@/activity-log';

// add the coq mode to codemirror
import './codemirror/CoqCodemirrorMode';

import VueRouter from 'vue-router';
import routes from './router';

writeActivity('startup');

Vue.config.productionTip = false;
Vue.use(require('vue-shortkey'));
Vue.use(Vuex);
Vue.use(BootstrapVue);
Vue.use(VueRouter);

import store from './store/store';

// We import this here (instead of via style-resources-loader) to prevent
// duplication.
import './assets/sass/main.scss';

const router = new VueRouter(routes);
router.afterEach((to, from) => {
  const location = to.query.location;
  writeActivity('navigation', {
    to: to.name,
    location: location,
  });
});

let url = window.location.href;

if (url.endsWith('#/')) {
  url = url.substr(0, url.length - 2);
}

if (url.indexOf('?') >= 0) {
  const parts = url.split('?', 2)[1].split('&');

  for (const part of parts) {
    if (part.startsWith('location=')) {
      const location = decodeURIComponent(part.replace('location=', ''));
      router.replace({name: 'edit', query: {location}});
    }
  }
}

new Vue({
  store: new Vuex.Store(store),
  router,
  render: (h) => h(App),
}).$mount('#app');
