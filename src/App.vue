<template>
    <div style="width: 100%; height: 100%">
        <router-view></router-view>
        <loader></loader>
    </div>
</template>

<script>
import Loader from './pageless/Loader';
export default {
  name: 'App',
  components: {Loader},
};
</script>
