<template>
    <div>
        <b-dropdown-item
          :title="buttonInfo.disabled ? '' : titleText"
          :class="{'disabled': buttonInfo.disabled}"
          @click="sendEvent" href="javascript:void(0)">
            <div v-shortkey="shortcut" @shortkey="sendEvent"
                      :class="{'disabled': buttonInfo.disabled}"
                      class="button-info">
              {{ buttonInfo.text }}
            </div>
            <div class="topbar-shortcut">
                {{ formattedShortcut }}
            </div>
        </b-dropdown-item>
        <hr class="button-separator" v-if="buttonInfo.line">
    </div>
</template>

<script>
import ShortcutButton from './ShortcutButton.vue';

export default {
  name: 'TopbarButton',
  mixins: [ShortcutButton],
};
</script>

<style lang="scss" scoped>
  @import "../../../assets/sass/_colors.scss";
    .button-info {
        max-width: 250px;
        overflow: hidden;
        text-overflow: ellipsis;
    }

    .topbar-shortcut {
        padding-top: 3px;
        @include theme(font-family, font-stack-code);
        @include theme(color, color-gray);
        padding-left: 10px;
    }
</style>
