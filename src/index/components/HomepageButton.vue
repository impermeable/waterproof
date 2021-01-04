<template>
  <div class="homepage-button"
      :href="buttonInfo.target"
      v-shortkey="shortKey"
      @shortkey="openNotebook"
      @click="openNotebook">
    <img
        class="homepage-button-icon"
        v-bind:alt="buttonInfo.text"
        v-bind:src="buttonInfo.image"
    />
    <span class="homepage-button-text">{{ buttonInfo.text }}</span>
  </div>
</template>

<script>
const {dialog} = require('electron').remote;
import ShortKeys from '../../io/shortKey';

export default {
  name: 'HomepageButton',
  props: {
    buttonInfo: Object,
    shortKeys: ShortKeys,
  },
  methods: {
    choosePath: function() {
      const options = {
        filters: [
          {
            name: 'Waterproof files',
            extensions: ['wpn', 'wpe'],
          },
          {
            name: 'Waterproof notebooks',
            extensions: ['wpn'],
          },
          {
            name: 'Waterproof exercise',
            extensions: ['wpe'],
          },
          {
            name: 'All files',
            extensions: ['*'],
          },
        ],
        properties: ['openFile'],
      };

      const filePaths = dialog.showOpenDialogSync(options);
      let filePath;
      if (filePaths) {
        filePath = filePaths[0];
      }

      return filePath;
    },
    openNotebook: function() {
      if (this.buttonInfo.open) {
        const filePath = this.choosePath();

        if (!filePath) {
          return;
        }
        this.$router.push(Object.assign(
            {query: {location: filePath}}, this.buttonInfo.target));
      } else {
        this.$router.push(this.buttonInfo.target);
        // window.location = this.buttonInfo.target;
      }
    },
  },
  computed: {
    shortKey: function() {
      return this.shortKeys.shortKeys[this.buttonInfo.shortKeyTag];
    },
  },
};
</script>

<style lang="scss">
@import '../../assets/sass/_colors.scss';
/**
 * (1) Ensure padding does not interfere with icon size.
 * (2) Allow explicit sizing of inline element.
 */
.homepage-button {
  box-sizing: content-box; /* 1 */
  @include theme(color, color-primary);
  display: block; /* 2 */
  padding: 10px; /* 1 */
  text-align: center;
  width: 128px; /* 2 */

  /**
   * Ensure image scales with parent element width.
   */
  &-icon {
    height: auto;
    max-width: 100%;
  }

  /**
   * Ensure text is vertically centered.
   */
  &-text {
    @include theme(color, color-text-on-primary);
    display: flex;
    justify-content: center;
  }

  /**
   * EXPERIMENTAL: Alternate hover effect: Colored, rounded background box.
   */
  &:hover {
    @include theme(background-color, color-primary);
    border-radius: 10px;

    > * {
      filter: brightness(0) invert(1); /* Make text and logo white. */
    }
  }

  @include respond-to(sm-lower) {
    width: 100%;
    display: flex;
    align-items: center;

    &-icon {
      width: 48px;
    }

    &-text {
      margin-left: 1rem;
    }
  }

  @include respond-to(lg) {
    width: 192px;
  }
}
</style>
