import Index from './index/Index';
import Edit from './editpage/Edit';

export default {
  routes: [
    {
      path: '/',
      name: 'home',
      component: Index,
    },
    {
      path: '/edit',
      name: 'edit',
      component: Edit,
    },
    {
      path: '*',
      redirect: '/',
    },
  ],
};
