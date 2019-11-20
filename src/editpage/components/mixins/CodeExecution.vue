<script>
export default {
  name: 'CodeExecution',
  methods: {
    refreshExecStatus: function(animation = true) {
      if (this.executeIndex < 0) {
        this.executed = false;
        this.execHeight = 0;
        this.execHeightBall = 0;
        return;
      }

      this.executed = true;
      this.alignGutter(animation);
    },
  },
};
</script>
