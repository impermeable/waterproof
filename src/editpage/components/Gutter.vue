<template>
  <div :style="{height: height + 'px'}"
       :class="{'no-exec': !executed, 'exec-gutter': true}">
    <template v-if="executed">
      <div class="exec-ball"></div>
      <div :class="['exec-bar', {'no-transition': !ani}]"
           :style="{height: execHeight + 'px'}"></div>
      <div :class="['exec-ball', {'no-transition': !ani}]"
           :style="{top: execHeightBall  + 'px'}"></div>
      <div :class="['pending-bar', {'no-transition': !ani}]"
           :style="{height: (pendingHeight - 7) + 'px'}"></div>
      <div :class="['pending-ball', {'no-transition': !ani}]"
           :style="{top: (pendingHeightBall)  + 'px'}"></div>
    </template>
  </div>
</template>
<script>
export default {
  name: 'Gutter',
  props: {
    ani: {},
    execHeight: {},
    execHeightBall: {},
    executed: {},
    height: {},
    pendingHeight: {},
    pendingHeightBall: {},
  },
};
</script>
