<template>
    <div>
        <b-dropdown-item
          :title="buttonInfo.disabled ? '' : titleText"
          :class="{'topbar-button': true, 'disabled': buttonInfo.disabled}"
          @click="sendEvent" href="javascript:void(0)">
            <div v-shortkey="shortcut" @shortkey="sendEvent"
                      :class="{'disabled': buttonInfo.disabled}">
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

<style scoped>

    .topbar-shortcut {
        padding-top: 3px;
        font-family: monospace;
        color: gray;
        padding-left: 10px;
    }

    a.disabled {
      color: gray;
    }
</style>
