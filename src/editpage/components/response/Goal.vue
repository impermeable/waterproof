<template>
  <div class="goal" @click="opened = !opened">
    <div ref="hypoth" :class="{hypothesis: true}" v-html="hypothesis"></div>
    <div class="hrfake">
      <span class="goal-id">({{index + 1}}/{{total}})</span>
    </div>
    <div :class="{opened: opened, 'opened-tick': true}" ref="opentick">▶</div>
    <span class="goal-target" v-html="subGoal"></span>
  </div>
</template>

<script>
export default {
  name: 'Goal',
  props: {
    goal: String,
    index: Number,
    total: Number,
  },
  data: function() {
    return {
      opened: true,
      instant: false,
    };
  },
  created: function() {
    this.opened = this.index === 0;
    if (!this.opened) {
      this.instant = true;
    }
  },
  computed: {
    parts: function() {
      return this.goal.split(/={28}/);
    },
    hypothesis: function() {
      if (this.parts.length > 0) {
        return this.parts[0].trim().replace(/\n/g, '<br>');
      }
    },
    subGoal: function() {
      if (this.parts.length > 1) {
        return this.parts[1].trim().replace(/\n/g, '<br>');
      }
    },
  },
  watch: {
    opened: function(shouldOpen) {
      const element = this.$refs.hypoth;

      if (shouldOpen) {
        this.expandHypothesis(element);
      } else {
        this.collapseHypothesis(element);
      }

      if (this.instant) {
        this.instant = false;
      }
    },
  },
  methods: {
    expandHypothesis: function(element) {
      const sectionHeight = element.scrollHeight;

      // have the element transition to the height of its inner content
      element.style.height = sectionHeight + 'px';

      element.addEventListener('transitionend', function expandTransition() {
        element.removeEventListener('transitionend', expandTransition);

        // return height to auto
        element.style.height = null;
      });
    },
    collapseHypothesis: function(element) {
      const sectionHeight = element.scrollHeight;
      const elementTransition = element.style.transition;
      const instant = this.instant;
      element.style.transition = '';

      // explicitly set the element's height to its current pixel height
      requestAnimationFrame(function() {
        element.style.transition = elementTransition;
        if (instant) {
          element.style.height = 0 + 'px';
        } else {
          element.style.height = sectionHeight + 'px';

          // height to 0 with animation
          requestAnimationFrame(function() {
            element.style.height = 0 + 'px';
          });
        }
      });
    },
  },
};
</script>

<style lang="scss" scoped>

  $fold-animate-time: 0.3s;

  .openGoal {
    /*padding-top: 0;*/
  }

  .hrfake {
    border-bottom: 1px solid black;
    text-align: right;
  }

  .opened-tick {
    transition: transform $fold-animate-time ease-in-out;
    margin-right: 10px;
    display: inline-block;
  }

  .opened {
    transform: rotate(-90deg);
  }

  .hypothesis {
    padding-left: 2.5em;
    overflow:hidden;
    transition:height $fold-animate-time ease-in-out;
    height:auto;
    margin-bottom: -1.3em;
  }

  .goal-target {
    margin-top: 0.3em;
    margin-left: 1em;
  }

  .instant {
    transition: none !important;
  }

</style>
