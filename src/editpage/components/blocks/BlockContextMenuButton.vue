<template>
  <li class="context-menu-button">
    <hr v-if="buttonInfo === null"/>
    <a v-else-if="!buttonInfo.active()" class="not-active" href="#">
      <span> {{buttonInfo.text}} </span>
      <span> {{formattedShortcut}} </span>
    </a>
    <a v-else href="#"
        @click.prevent="buttonInfo.action"
        v-shortkey="buttonInfo.disableShortkey? [] : shortcut"
        @shortkey="buttonInfo.action"
        :title="titleText">
      <span>{{buttonInfo.text}}</span>
      <span>{{formattedShortcut}}</span>
    </a>
  </li>
</template>

<script>
import ShortcutButton from '../menubars/ShortcutButton';

export default {
  name: 'BlockContextMenuButton',
  mixins: [ShortcutButton],
};
</script>

<style lang="scss">
  li.context-menu-button > hr {
    margin: 2px;
  }

  li.context-menu-button > a {
    padding: 2px 12px;
    display: flex !important;
    justify-content: space-between;
    font-size: 16px;

    &:hover {
      background-color: $color-primary-light;
      color: $color-on-primary;
    }
  }

  .not-active {
    color: $color-primary-extra-light !important;
    cursor: default;

    &:hover {
      background-color: $color-gray-light !important;
      color: $color-primary-extra-light !important;
    }
  }
</style>
