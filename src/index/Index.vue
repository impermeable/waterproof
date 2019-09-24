<template>
  <div class="app" id="home">
    <div class="sidebar">
      <h3>Recent files</h3>
      <ul class="recent-files">
        <span v-if="this.recents.fileLoading">Loading...</span>
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

export default {
  name: 'app',
  components: {
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
          target: 'editpage.html',
          shortKeyTag: 'newFile',
        },
        {
          id: 1,
          text: 'Open notebook',
          image: require('../assets/images/openfile.svg'),
          target: 'editpage.html',
          open: true,
          shortKeyTag: 'loadFile',
        },
        {
          id: 2,
          text: 'Waterproof tutorial',
          image: require('../assets/images/tutorial.svg'),
          target: 'editpage.html?Tutorial',
          shortKeyTag: 'tutorial',
        },
      ],
      fileLoading: true,
      recents: new Recents(),
      shortKeys: new ShortKeys(),
    };
  },
};
</script>

<style lang="scss">
.app#home {
  @include flex-style(row);
  height: 100vh;
  overflow: hidden;

  .sidebar {
    flex: 0 0 auto;
    padding: 1.5rem;
    width: 250px;

    background: $color-primary;
    color: $color-on-primary;

    @include respond-to(xs) {
      display: none;
    }

    .recent-files {
      border-bottom: 1px solid $color-on-primary;
      border-top: 1px solid $color-on-primary;
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
