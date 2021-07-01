<template>
  <div>
      <img alt="Waterproof" class="logo"
            src="../../assets/images/Waterprooflogo.svg"/>
      <div class="about-content">
        <p>
          Waterproof is created using JavaScript, HTML and CSS.
          It is built as an Electron app, using the Vue.js and
          Bootstrap frameworks.
        </p>
        <p>
          Waterproof was originally created and developed by Team ChefCoq as a
          Software Engineering Project at Eindhoven University of Technology.
          The project was created for Dr. J.W. Portegies.
        </p>
        <p>
          The project was subsequently imporved as part of Team Waterfowl's
          Software Engineering Project at Eindhoven University of Technology.
        </p>
        <p>
          Waterproof uses the following technologies:
        </p>
        <ul>
          <li><a href="#" @click="openPage('https://github.com/coq/coq')">Coq 8.9.0</a></li>
          <li><a href="#" @click="openPage('https://github.com/ejgallego/coq-serapi')">Coq-serapi</a></li>
          <li>Markdown</li>
          <li><a href="#" @click="openPage('https://github.com/KaTeX/KaTeX')">KaTeX</a></li>
        </ul>
        <div class="row">
        <p class="col">
          <b>Team Waterfowl 🦆</b><br>
          A. Castella <br>
          A. Cucoș<br>
          C. Manea<br>
          N. van der Meer<br>
          L. Pirée<br>
          T. Trouwen<br>
          T. Voicu<br>
          M. Țifrea<br>
          A. S. Vrămuleț<br>
          Y. Zeng<br>
        </p>
        <p class="col">
          <b>Team ChefCoq 🧑‍🍳</b><br>
          T.P.J. Beurskens<br>
          B.W.T. Gieling<br>
          S.P. Gunter<br>
          M.L. Hofsté<br>
          H.A. Melchers<br>
          A.I.O. Nijsten<br>
          R.F. Schmiermann<br>
          E.C. Takke<br>
          D.A. Tuin<br>
          R.F.A. Verhaegh<br>
          G.C. van Wordragen<br>
        </p>
        </div>
        <p>
          Version: {{versionNumber}}
        </p>
      </div>
    </div>
</template>

<script>

export default {
  name: 'About',
  methods: {
    openPage: function(link) {
      require('electron').shell.openExternal(link);
    },
  },
  computed: {
    versionNumber: function() {
      return require('electron').remote.app.getVersion();
    },
  },
};
</script>

<style lang="scss" scoped>
  .about-content {
    font-size: 14px;
  }
  .logo {
    max-height: 80px;
  }

  .col {
    float: left;
    width: 50%;
  }

  /* Clear floats after the columns */
  .row:after {
    content: "";
    display: table;
    clear: both;
  }
</style>


