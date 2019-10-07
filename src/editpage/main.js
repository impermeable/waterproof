import Vue from 'vue';
import Vuex from 'vuex';
import App from './Edit.vue';
import store from '../store';
import BootstrapVue from 'bootstrap-vue';

// add the coq mode to codemirror
import '../codemirror/tex-input';
import '../codemirror/CoqCodemirrorMode';

// We import this here (instead of via style-resources-loader) to prevent
// duplication.
import '../assets/sass/main.scss';

Vue.config.productionTip = false;
Vue.use(Vuex);
Vue.use(BootstrapVue);
Vue.use(require('vue-shortkey'));

new Vue({
  store,
  render: (h) => h(App),
}).$mount('#app');
