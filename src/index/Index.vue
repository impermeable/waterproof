<template>
  <div class="app" id="home">
    <div class="sidebar">
      <h3>Recent files</h3>
      <ul class="recent-files">
        <li style="list-style: none;" v-if="this.recents.fileLoading">
            Loading...
        </li>
        <recent-file
          v-else=""
          v-for="file in this.recents.filelist"
          v-bind:fileInfo="file"
          v-bind:key="file.id"
        ></recent-file>
      </ul>
    </div>
    <div class="container">
      <div class="logo-container">
        <img alt="Waterproof" class="logo"
             src="../assets/images/Waterprooflogo.svg"/>
      </div>
      <div class="buttons">
        <homepage-button
          v-for="button in buttonlist"
          v-bind:buttonInfo="button"
          v-bind:key="button.id"
          v-bind:shortKeys="shortKeys"
        ></homepage-button>
      </div>
    </div>
  </div>
</template>

<script>
import RecentFile from './components/RecentFile';
import HomepageButton from './components/HomepageButton';
import Recents from '../io/recents';
import ShortKeys from '../io/shortKey';
import Loader from '../pageless/Loader';

export default {
  name: 'app',
  components: {
    Loader,
    RecentFile,
    HomepageButton,
  },
  data: function() {
    return {
      buttonlist: [
        {
          id: 0,
          text: 'Create a new notebook',
          image: require('../assets/images/newfile.svg'),
          target: {name: 'edit'},
          shortKeyTag: 'newFile',
        },
        {
          id: 1,
          text: 'Open notebook',
          image: require('../assets/images/openfile.svg'),
          target: {name: 'edit'},
          open: true,
          shortKeyTag: 'loadFile',
        },
        {
          id: 2,
          text: 'Waterproof tutorial',
          image: require('../assets/images/tutorial.svg'),
          target: {name: 'edit', query: {location: 'Tutorial'}},
          shortKeyTag: 'tutorial',
        },
      ],
      fileLoading: true,
      recents: new Recents(),
      shortKeys: new ShortKeys(),
      shutdownHook: null,
    };
  },
  created: function() {
    if (process.env.NODE_ENV !== 'test' &&
            process.env.NODE_ENV !== 'coverage') {
      this.shutdownHook = () => {
        ipcRenderer.send('confirmClosing');
      };
      // cant import this in tests, :/ very ugly solution
      const ipcRenderer = require('electron').ipcRenderer;
      ipcRenderer.on('closing-application', this.shutdownHook);
    }
  },
  beforeDestroy() {
    require('electron').ipcRenderer
        .removeListener('closing-application', this.shutdownHook);
  },
};
</script>

<style lang="scss">
@import '../assets/sass/_colors.scss';

.app#home {
  @include flex-style(row);
  height: 100vh;
  overflow: hidden;
  /*position: relative;*/

  .sidebar {
    flex: 0 0 auto;
    padding: 1.5rem;
    width: 250px;

    @include theme(background-color, color-primary);
    @include theme(color, color-text-in-primary);

    @include respond-to(xs) {
      display: none;
    }

    .recent-files {
      @include theme(border-bottom, color-text-in-primary, 1px solid);
      @include theme(border-top, color-text-in-primary, 1px solid);
      padding-inline-start: 0;

      .recent-file {
        text-overflow: ellipsis;
        overflow: hidden;
      }
    }
  }

  .container {
    @include flex-style(column);
    align-items: stretch;
    flex: 1 0 0;

    .logo-container {
      align-items: center;
      display: flex;
      height: 40%;
      justify-content: center;

      .logo {
        box-sizing: content-box;
        flex: 0 0 auto;
        height: 150px;
        width: auto;
        padding: 25px;

        @include respond-to(sm) {
          padding: 37.5px;
          height: 100px;
        }

        @include respond-to(xs) {
          padding: 50px;
          height: 75px;
        }

        @include respond-to(lg) {
          padding: 12.5px;
          height: 175px;
        }
      }
    }

    .buttons {
      @include flex-style(row);
      flex: 1 0 0;
      justify-content: space-evenly;
      align-items: center;

      @include respond-to(sm-lower) {
        flex-direction: column;
      }
    }

    @include respond-to(sm-lower) {
      align-items: center;
    }
  }
}
</style>
