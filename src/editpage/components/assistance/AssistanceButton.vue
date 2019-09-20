<template>
  <div class="assistance-button"
    :class="{big: big}"
    @click="action"
  >
    <!-- <img :src="icon" class="button-icon" /> -->
    {{name}}
  </div>
</template>

<script>
export default {
  name: 'AssistanceButton',
  props: ['name', 'icon', 'action', 'big'],
};
</script>

<style lang="scss">
  .assistance-button {
    background-color: $color-primary-light;
    color: $color-on-primary;
    cursor: pointer;
    // border: 0.5px solid black;
    flex: 1 0 33%;
    padding: 2px;
    font-size: 18px;
    text-align: center;
    transition: 0.3s;

    &:hover {
      background-color: $color-primary;
    }

    .button-icon {
      width: 20px;
    }
  }

  .big {
    flex-basis: 66%;
  }
</style>
