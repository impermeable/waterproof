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
          Waterproof is created and developed by Team ChefCoq as a
          Software Engineering Project at Eindhoven University of Technology.
          The project was created for Dr. J.W. Portegies.
        </p>
        <p>
          Waterproof uses the following technologies:
        </p>
        <ul>
          <li>Coq 8.9.0</li>
          <li><a href="#" @click="openPage('https://github.com/ejgallego/coq-serapi')">Coq-serapi</a></li>
          <li>Markdown</li>
          <li>KaTeX</li>
        </ul>
        <p>
          <b>Team ChefCoq</b><br>
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
};
</script>

<style lang="scss" scoped>
  .about-content {
    font-size: 14px;
  }
</style>


