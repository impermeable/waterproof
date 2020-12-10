<template>
  <div v-bind:class="{ sidebar: true, 'sidebar-wide': tooltips }">
    <sidebar-button
      v-for="button in buttons"
      v-bind:buttonInfo="button" v-bind:shortKeys="shortKeys"
      v-bind:key="button.text" v-bind:tooltip="tooltips"
      v-bind:event-bus="eventBus">
    </sidebar-button>

    <!--  Button to switch the tooltips  -->
    <sidebar-button
      :button-info="toolTipSwitchButton"
      :shortKeys="shortKeys" :tooltip="tooltips"
      :class="{flipped: tooltips, foldButton: true}"
      :event-bus="eventBus">
    </sidebar-button>
  </div>
</template>

<script>
import SidebarButton from './SidebarButton';

export default {
  name: 'Sidebar',
  props: ['shortKeys', 'eventBus'],
  components: {
    SidebarButton,
  },
  data: function() {
    return {
      tooltips: true,
      toolTipSwitchButton: {
        text: 'Hide tooltips',
        icon: require('../../../assets/images/tooltipExpand.svg'),
        eventType: 'swap-tooltips',
        requires: [],
        shortkeyTag: 'foldTooltips',
      },
      buttons: [
        {
          text: 'Execute next',
          icon: require('../../../assets/images/arrowNext.svg'),
          event: 'coqNext',
          eventType: 'on-proof-window',
          requires: ['notebook', 'coq-ready'],
          shortkeyTag: 'executeNext',
        },
        {
          text: 'Execute previous',
          icon: require('../../../assets/images/arrowPrevious.svg'),
          event: 'coqPrev',
          eventType: 'on-proof-window',
          requires: ['notebook', 'coq-ready'],
          shortkeyTag: 'executePrev',
        },
        {
          text: 'Execute to cursor',
          icon: require('../../../assets/images/arrowToCursor.svg'),
          event: 'coqToCursor',
          eventType: 'on-proof-window',
          requires: ['notebook', 'coq-ready'],
          shortkeyTag: 'executeToCursor',
        },
        {
          text: 'Execute all',
          icon: require('../../../assets/images/arrowDoubleRight.svg'),
          event: 'coqAll',
          line: 'true',
          eventType: 'on-proof-window',
          requires: ['notebook', 'coq-ready'],
          shortkeyTag: 'executeAll',
        },
        {
          text: 'Zoom in',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          shortkeyTag: 'zoomIn',
          event: 'zoomIn',
          eventType: 'settings',
          requires: [],
        },
        {
          text: 'Zoom out',
          icon: require('../../../assets/images/looking_glass_grey.svg'),
          shortkeyTag: 'zoomOut',
          event: 'zoomOut',
          eventType: 'settings',
          requires: [],
          line: true,
        },
        {
          text: 'Next input',
          icon: require('../../../assets/images/nextInput.svg'),
          event: 'nextInput',
          eventType: 'on-proof-window',
          requires: ['notebook'],
          shortkeyTag: 'nextInput',
        },
        {
          text: 'Previous input',
          icon: require('../../../assets/images/previousInput.svg'),
          event: 'previousInput',
          line: 'true',
          eventType: 'on-proof-window',
          requires: ['notebook'],
          shortkeyTag: 'previousInput',
        },
        {
          text: 'Insert code',
          icon: require('../../../assets/images/codeButton.svg'),
          event: 'insertCode',
          eventType: 'on-proof-window',
          requires: ['notebook'],
          shortkeyTag: 'insertCode',
        },
        {
          text: 'Insert text',
          icon: require('../../../assets/images/textButton.svg'),
          event: 'insertText',
          eventType: 'on-proof-window',
          requires: ['notebook'],
          shortkeyTag: 'insertText',
        },
        {
          text: 'Insert hint',
          icon: require('../../../assets/images/bulbOff.svg'),
          event: 'insertHint',
          eventType: 'on-proof-window',
          requires: ['no-exercise-sheet'],
          shortkeyTag: 'insertHint',
        },
        {
          text: 'Insert input',
          icon: require('../../../assets/images/lock_unlocked.svg'),
          event: 'insertInputArea',
          line: 'true',
          eventType: 'on-proof-window',
          requires: ['no-exercise-sheet'],
          shortkeyTag: 'insertInputArea',
        },
        {
          text: 'Tutorial page',
          icon: require('../../../assets/images/tutorialButton.svg'),
          event: 'openTutorial',
          eventType: 'on-edit',
          requires: [],
          shortkeyTag: 'tutorialPage',
        },
        {
          text: 'Find in notebook',
          icon: require('../../../assets/images/findButton.svg'),
          event: 'findAndReplace',
          eventType: 'on-proof-window',
          requires: [],
          tooltip: true,
          findAndReplace: 'find',
        },
        {
          text: 'Settings',
          icon: require('../../../assets/images/findButton.svg'),
          event: 'openSettingsModal',
          eventType: 'settings',
          requires: [],
          tooltip: true,
        },
      ],
    };
  },
  mounted: function() {
    this.eventBus.$on('notebook-opened', this.updateButtons);
    this.eventBus.$on('swap-tooltips', this.swapTooltips);

    if (window.localStorage.getItem('tooltips-hidden')) {
      this.tooltips = false;
    }
  },
  methods: {
    /**
     * Toggles the tooltips in the sidebar on and off
     */
    swapTooltips: function() {
      this.tooltips = !this.tooltips;
      window.localStorage.setItem('tooltips-hidden', this.tooltips);
    },
    updateButtons: function(status) {
      // For each button, enable it if all requirements are met
      for (const button of this.buttons) {
        const isEnabled = button.requires.every(
            (requirement) => status.includes(requirement)
        );
        // If disabled does not start in the object vue does not know about it
        this.$set(button, 'disabled', !isEnabled);
      }
    },
  },
};
</script>

<style lang="scss">
@import "../../../assets/sass/pages/_edit";

  .sidebar {
    background-color: #2b3990;
    padding-top: $tab-height-large;
    min-width: 40px;
    position: relative;

    @include respond-to(sm-lower) {
      min-width: 30px;
      padding-top: $tab-height-small;
    }
  }

  .sidebar-wide {
    min-width: 150px;

    .foldButton {
      min-width: 150px;
    }

  }

  .foldButton {
    position: absolute;
    bottom: 5px;
  }

</style>
