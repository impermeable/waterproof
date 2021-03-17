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
        <table style='margin: 0px; padding: 0px'>
          <tr>
            <th>
              <h6>Zoom:</h6>
            </th>
            <th style='width: 50%'>
              <h6>{{zoomLevel}}</h6>
            </th>
            <th style='width: 100px'>
              <button style='width: 49%; height: 40px; margin-right: 1%'
                class='settings-modal-button'
                @click="zoomIn"> + </button>
              <button style='width: 49%; height: 40px; margin-left: 1%'
                class='settings-modal-button'
                @click="zoomOut"> - </button>
            </th>
          </tr>
          <tr>
            <th>
              <h6>Theme:</h6>
            </th>
            <th style='width: 50%'>
              <h6>{{currentTheme}}</h6>
            </th>
            <th style='width: 100px'>
              <div style='width: 100%' class="dropdown">
                <button style='width: 100%; height: 40px'
                  class="dropbtn settings-modal-button">Select</button>
                <div class="dropdown-content">
                  <a v-for="style in styles" :key="style"
                      @click="changeTheme(style)">
                      {{style}}</a>
                </div>
              </div>
            </th>
          </tr>
        </table>
        <h4 style='margin-top: 10%'>
            Configuration
        </h4>
        <table>
          <tr v-for="setting in configurationString"
                    :key="setting.name">
            <td style='padding-right: 20px;'
                v-if="setting.type === 'Dependency'"
                :title="setting.name">{{setting.name}}</td>
            <td v-if="setting.type === 'Dependency'"
                :title="setting.val">{{setting.val}}</td>
          </tr>
        </table>
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
    };
  },
  methods: {
    closeSettingsModal: function() {
      document.getElementById('settingsModal').style.display = 'none';
    },

    openSettingsModal: function() {
      document.getElementById('settingsModal').style.display = 'block';
      this.updateConfigurationString();
      // const release = await store.state.lock.acquire();

      // release();
    },

    zoomIn: function() {
      this.zoomChange(1.1);
    },

    zoomOut: function() {
      this.zoomChange(1/1.1);
    },

    zoomSliderChanged: function() {
      const val = parseFloat(this.zoomSliderValue);
      this.$store.commit('setZoom', val);
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
  },
  computed: {
    zoomLevel() {
      const settings = this.$store.state.settings;
      return settings.zoom.toPrecision(3);
    },
    currentTheme() {
      const settings = this.$store.state.settings;
      return settings.theme;
    },
    configurationString() {
      const libs = this.$store.state.libraries;
      const settings = this.$store.state.settings;
      return [
        {
          name: 'Sertop path',
          val: libs.sertopPath,
          type: 'Dependency',
        },
        {
          name: 'Serapi version',
          val: libs.serapiVersion,
          type: 'Dependency',
        },
        {
          name: 'Library version',
          val: libs.libraryVersion,
          type: 'Dependency',
        },
        {
          name: 'Zoom',
          val: settings.zoom.toPrecision(2),
          type: 'Zoom',
        },
        {
          name: 'Theme',
          val: settings.theme,
          type: 'Theme',
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
    background-color: rgba(0,0,0,0.95); /* Partly opaque background */
    display: none; /* Hidden by default */
    position: fixed; /* Stay in place */
    z-index: 1; /* Sit on top */
    left: 0;
    top: 0;
    width: 100%; /* Full width */
    height: 100%; /* Full height */
    overflow: auto; /* Enable scroll if needed */
  }

  /* Modal Content/Box */
  #settingsModalContent {
    @include theme(background-color, color-background);
    margin: 15% auto; /* 15% from the top and centered */
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

</style>
