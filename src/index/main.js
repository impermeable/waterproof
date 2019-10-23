import Vue from 'vue';
import App from './Index.vue';
import store from '../store';

// We import this here (instead of via style-resources-loader) to prevent
// duplication.
import '../assets/sass/main.scss';

Vue.config.productionTip = false;
Vue.use(require('vue-shortkey'));

new Vue({
  store,
  render: (h) => h(App),
}).$mount('#app');
