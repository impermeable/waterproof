<template>
    <div id="settingsModal" class="modal" @click="closeSettingsModal">
      <!-- Modal content -->
      <div id="settingsModalContent" @click.stop>
        <button id="closeSettingsModalButton" class="settings-modal-button"
            @click="closeSettingsModal">
          &times;
        </button>
        <p id="settingsOverview">
        </p>
        <h3>
          View options
        </h3>
        <table style='width: 50%; padding: 0;'
               class="alternateRows">
          <tr>
            <td>
              <h6>Zoom:</h6>
            </td>
            <td style='width: 50%; min-width: 60px'>
              <h6>{{ (zoomLevel * 100).toFixed(0)}} %</h6>
            </td>
            <td style='min-width:120px'>
              <button style='width: 25%; height: 40px;'
                class='settings-modal-button'
                @click="zoomIn"> + </button>
              <button style='width: calc(50% - 4px);
              height: 40px; margin: 1px 2px;'
                      class='settings-modal-button'
                      @click="resetZoom">Reset</button>
              <button style='width: 25%; height: 40px;'
                class='settings-modal-button'
                @click="zoomOut"> - </button>
            </td>
          </tr>
          <tr>
            <td>
              <h6>Theme:</h6>
            </td>
            <td>
              <h6>{{currentTheme}}</h6>
            </td>
            <td>
              <div style='width: 100%' class="dropdown">
                <button style='width: 100%; height: 40px'
                  class="dropbtn settings-modal-button">
                  <span>{{currentTheme}}</span>
                  <span style="float: right">&blacktriangledown;</span>
                </button>
                <div class="dropdown-content" style="width: 100%">
                  <a v-for="style in styles" :key="style"
                      @click="changeTheme(style)">
                      {{style}}</a>
                </div>
              </div>
            </td>
          </tr>
          <tr>
            <td>
              <h6>Goals:</h6>
            </td>
            <td style='width: 50%; min-width: 60px'>
              <h6>{{currentGoalStyle}}</h6>
            </td>
            <td>
              <div style='width: 100%' class="dropdown">
                <button style='width: 100%; height: 40px'
                  class="dropbtn settings-modal-button">
                  <span>{{currentGoalStyle}}</span>
                  <span style="float: right">&blacktriangledown;</span>
                </button>
                <div class="dropdown-content" style="width: 100%">
                  <a v-for="goalStyle in goalStyles" :key="goalStyle"
                      @click="changeGoalStyle(goalStyle)">
                      {{goalStyle}}</a>
                </div>
              </div>
            </td>
          </tr>
        </table>
        <h4 style='margin-top: 10%'>
            Configuration
        </h4>
        <div style="overflow-y: scroll; max-height: 10%">
          <table class="alternateRows" style="width: 100%">
            <tr v-for="setting in configurationString"
                :key="setting.name">
              <td style='padding-right: 20px;'
                  :title="setting.name">{{setting.name}}</td>
              <td :title="setting.val">{{setting.val}}</td>
            </tr>
          </table>
        </div>
      </div>
    </div>
</template>


<script>
export default {
  name: 'SettingsModal',
  components: {},
  props: {
    eventBus: Object,
  },
  data: function() {
    return {
      zoomMin: 0.3,
      zoomMax: 3,
      zoomSliderValue: 0,
      styles: ['light', 'dark', 'light_roboto', 'dark_roboto'],
      goalStyles: ['all', 'goal', 'none'],
    };
  },
  methods: {
    closeSettingsModal: function() {
      document.getElementById('settingsModal').style.display = 'none';
    },

    openSettingsModal: function() {
      document.getElementById('settingsModal').style.display = 'block';
    },

    zoomIn: function() {
      this.zoomChange(1.1);
    },

    zoomOut: function() {
      this.zoomChange(1/1.1);
    },

    resetZoom() {
      this.$store.commit('setZoom', 1.0);
    },

    zoomChange: function(factor) {
      const newZoom = this.$store.state.settings.zoom * factor;

      const boundedZoom = Math.max(0.3, Math.min(newZoom, 3.0));
      this.$store.commit('setZoom', boundedZoom);
      this.updateConfigurationString();
    },

    changeTheme: function(theme) {
      if (this.styles.includes(theme)) {
        this.$store.commit('setTheme', theme);
      }
    },

    changeGoalStyle: function(goalStyle) {
      if (this.goalStyles.includes(goalStyle)) {
        this.$store.commit('setGoalStyle', goalStyle);
      }
    },
  },
  computed: {
    zoomLevel() {
      const settings = this.$store.state.settings;
      return settings.zoom.toPrecision(3);
    },
    currentTheme() {
      return this.$store.state.settings.theme;
    },
    currentGoalStyle() {
      return this.$store.state.settings.goalStyle;
    },
    configurationString() {
      const libs = this.$store.state.libraries;
      return [
        {
          name: 'Sertop path',
          val: libs.sertopPath,
        },
        {
          name: 'Serapi version',
          val: libs.serapiVersion,
        },
        {
          name: 'Library version',
          val: libs.libraryVersion,
        },
      ];
    },
  },
  mounted: function() {
    this.zoomSliderValue = this.$store.state.settings.zoom;
    this.eventBus.$on('zoomIn', this.zoomIn);
    this.eventBus.$on('zoomOut', this.zoomOut);
    this.eventBus.$on('openSettingsModal', this.openSettingsModal);
  },
};
</script>

<style lang="scss">
  @import '../../../assets/sass/pages/edit';

  /* The Modal (background) */
  #settingsModal {
    background-color: rgba(0,0,0,0.75); /* Partly opaque background */
    display: none; /* Hidden by default */
    position: fixed; /* Stay in place */
    z-index: 10; /* Sit on top */
    left: 0;
    top: 0;
    width: 100%; /* Full width */
    height: 100%; /* Full height */
    overflow: auto; /* Enable scroll if needed */
  }

  /* Modal Content/Box */
  #settingsModalContent {
    @include theme(background-color, color-background);

    position: absolute;
    top: 50%; left: 50%;
    transform: translate(-50%,-50%);

    padding: 25px;
    @include theme(border, color-on-background, 2px solid);
    width: 60%; /* Could be more or less, depending on screen size */
    word-wrap: normal;
    font-size: small;
  }

  /* The Close Button */
  #closeSettingsModalButton {
    float: right;
    font-size: 28px;
    font-weight: bold;
  }

  .settings-modal-button {
    @include theme(background-color, color-background);
    @include theme(border, color-on-background, 2px solid);
    @include theme(color, color-on-background);
  }
  .settings-modal-button:hover {
  @include theme(background-color, color-gray-light)
}

  /** DROPDOWN START */
  .dropbtn {
  padding: 8px;
  font-size: 16px;
  border: none;
  cursor: pointer;
}

/* The container <div> - needed to position the dropdown content */
.dropdown {
  position: relative;
  display: inline-block;
}

h6 {
  padding-right: 10px;
}

/* Dropdown Content (Hidden by Default) */
.dropdown-content {
  display: none;
  position: absolute;
  @include theme(background-color, color-gray-light);
  @include theme(border, color-on-background, 1px solid);
  min-width: 160px;
  box-shadow: 0px 8px 16px 0px rgba(0,0,0,0.2);
  z-index: 1;
}

/* Links inside the dropdown */
.dropdown-content a {
  @include theme(color, color-on-background);
  padding: 12px 16px;
  text-decoration: none;
  display: block;
}

/* Change color of dropdown links on hover */
.dropdown-content a:hover {
  @include theme(background-color, color-gray)
}

/* Show the dropdown menu on hover */
.dropdown:hover .dropdown-content {
  display: block;
}
/** DROPDOWN END */

.alternateRows tr:nth-child(even) {
  @include theme(background-color, color-gray-light);
}

</style>
