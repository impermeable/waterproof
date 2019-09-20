<template>
  <a :title="titleText" @click="sendEvent">
    <div :class="{'sidebar-button': true, 'disabled': buttonInfo.disabled}"
     v-shortkey="shortcut" @shortkey="sendEvent"
     :key="buttonInfo.text + buttonInfo.disabled">
      <div class="tooltip-image image-masks"
           :style="{'-webkit-mask-image': 'url(' + buttonInfo.icon + ')'}">
      </div>
      <span class="button-tooltip" v-if="tooltip">
        {{ buttonInfo.text }}
      </span>
    </div>
    <hr class="button-separator" v-if="buttonInfo.line">
  </a>
</template>

<script>
import ShortcutButton from './ShortcutButton.vue';

export default {
  name: 'SidebarButton',
  mixins: [ShortcutButton],
  props: {
    tooltip: Boolean,
  },
};
</script>

<style lang="scss">

  .image-masks {
    mask-type: alpha;
    background-color: white;
    mask-repeat: no-repeat;
    -webkit-mask-repeat: no-repeat;
    -webkit-mask-position: center center;
    -webkit-mask-size: 40px 15px;
  }

  .button-tooltip {
    font-size: 12px;
    overflow: hidden;
    display: inline-block;
  }

  .tooltip-image {
    float: left;
    width: 40px;
    height: 25px;
    transition: transform 0.25s ease-in-out;
  }

  .disabled {

    .tooltip-image {
      background-color: darkgray;
    }

    color: darkgray !important;
  }

  hr.button-separator {
     border: 0;
     height: 1px !important;
     background: $color-primary-light;
     width: 80%;
     margin-bottom: 3px;
     margin-top: 3px;
     margin-right: 0;
     margin-left: 10%;
     display: block;
  }

  .flipped {
    .tooltip-image {
      transform: rotateY(180deg);
    }
  }

</style>
