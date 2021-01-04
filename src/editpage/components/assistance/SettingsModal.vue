<template>
    <div id="settingsModal" class="modal">
        <!-- Modal content -->
        <div id="settingsModalContent">
          <button id="closeSettingsModalButton" @click="closeSettingsModal">
            &times;
        </button>
          <!-- <h1>
            Settings
          </h1> -->
          <h3>
            Configuration
          </h3>
          <p id="settingsOverview">
          </p>
          <h3>
            View Settings
          </h3>
        <!-- <div class="slidecontainer">
            <input v-model="zoomSliderValue" type="range" min="0.3" max="3"
            step="0.1"
            value="50" class="slider" id="myRange" @change="zoomSliderChanged">
        </div> -->
        <table class='padding-table-columns'>
          <tr>
            <th><h5>Change the zoom level</h5></th>
            <th>
              <button class='settings-modal-button' @click="zoomIn">
                Zoom in
              </button>
              &nbsp;
              <button class='settings-modal-button' @click="zoomOut">
                Zoom out
              </button>
            </th>
          </tr>
          <tr>
            <th>
              <h5 style='padding-right: 50px;'>Toggle light and dark mode</h5>
            </th>
            <th>
              <button class='settings-modal-button' @click="toggleTheme">
                Toggle
              </button>
            </th>
          </tr>

        </table>
        </div>
    </div>
</template>


<script>
import Vue from 'vue';

export default {
  name: 'SettingsModal',
  components: {},
  props: {},
  data: function() {
    return {
      eventBus: new Vue(),
      zoomMin: 0.3,
      zoomMax: 3,
      zoomSliderValue: 0,
    };
  },
  methods: {
    forwardEvent: function(event) {
      console.log(event);
      this.eventBus.$emit(event);
      console.log('forwarded done');
    },
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

    toggleTheme: function() {
      const currClass = document.getElementsByTagName('HTML')[0]
          .getAttribute('class');
      if (currClass === 'dark') {
        this.$store.commit('setTheme', 'light');
      } else {
        this.$store.commit('setTheme', 'dark');
      }
      this.updateConfigurationString();
    },

    updateConfigurationString: function() {
      const libs = this.$store.state.libraries;
      const settings = this.$store.state.settings;
      document.getElementById('settingsOverview').innerHTML =
          'Sertop path: ' + libs.sertopPath + '<br /> Serapi Version: '
          + libs.serapiVersion + '<br /> Library Version: '
          + libs.libraryVersion + '<br /> Zoom: ' + settings.zoom
          + '<br /> Theme: ' + settings.theme;
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
    @include theme(border, color-gray-darkest, 2px solid);
    width: 60%; /* Could be more or less, depending on screen size */
    word-wrap: normal;
    font-size: small;
  }

  /* The Close Button */
  #closeSettingsModalButton {
    @include theme(background-color, color-white);
    @include theme(color, color-black);
    @include theme(border-color, color-black);
    float: right;
    font-size: 28px;
    font-weight: bold;
  }

  #closeSettingsModalButton:hover,
  #closeSettingsModalButton:focus {
    @include theme(color, color-black);
    text-decoration: none;
    cursor: pointer;
  }

  .settings-modal-button {
    @include theme(background-color, color-white);
    @include theme(border, color-black, 2px solid);
    @include theme(color, color-black);
  }

  .padding-table-columns td
  {
    padding:0 115px 0 0; /* Only right padding*/
  }

</style>
