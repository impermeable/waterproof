<template>
    <div id="settingsModal" class="modal">
        <!-- Modal content -->
        <div id="settingsModalContent">
        <button id="closeSettingsModalButton" @click="closeSettingsModal">
            &times;
        </button>
        <div class="slidecontainer">
            <input v-model="zoomSliderValue" type="range" min="0.3" max="3"
            step="0.1"
            value="50" class="slider" id="myRange" @change="zoomSliderChanged">
        </div>
        <button @click="zoomIn">
            Zoom in
        </button>
        <button @click="zoomOut">
            Zoom out
        </button>
        <p>Some text in the Modal..</p>
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
      this.$store.commit('setZoom', this.zoomSliderValue);
    },

    zoomChange: function(factor) {
      const newZoom = this.$store.state.settings.zoom * factor;

      const boundedZoom = Math.max(0.3, Math.min(newZoom, 3.0));
      this.$store.commit('setZoom', boundedZoom);
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
    background-color: rgb(0,0,0); /* Fallback color */
    background-color: rgba(0,0,0,0.4); /* Black w/ opacity */
  }

  /* Modal Content/Box */
  #settingsModalContent {
    background-color: #fefefe;
    margin: 15% auto; /* 15% from the top and centered */
    padding: 20px;
    border: 1px solid #888;
    width: 80%; /* Could be more or less, depending on screen size */
  }

  /* The Close Button */
  #closeSettingsModalButton {
    color: #aaa;
    float: right;
    font-size: 28px;
    font-weight: bold;
  }

  #closeSettingsModalButton:hover,
  #closeSettingsModalButton:focus {
    color: black;
    text-decoration: none;
    cursor: pointer;
  }

</style>
