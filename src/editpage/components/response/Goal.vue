<template>
  <div class="goal" @click="opened = !opened">
    <div v-show="showHypotheses">
      <ul class="hypothesis" ref="hypoth">
        <li v-for="hypo in  hypothesis" v-bind:key="hypo">
          <b> {{hypo.terms}} </b>
          {{hypo.type}}
        </li>
      </ul>
    </div>
    <div class="hrfake">
      <span class="goal-id">({{index + 1}}/{{total}})</span>
    </div>
    <div v-if="showHypotheses" :class="{opened: opened, 'opened-tick': true}">
      ▶
    </div>
    <span :class="{'goal-target': true,
      'goal-with-hypotheses': showHypotheses}"
          v-html="subGoal">
    </span>
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
      // TODO: IMPROVE CODE
      // TODO: fix line breaking
      // (using Coq / implementing own line breaking rules)
      let prevEndWithColon = false;
      const hypotheses = [];
      if (this.parts.length > 0) {
        const hypothesesParts = this.parts[0].split(/\n/g);

        for (const hypothesesPart of hypothesesParts) {
          // We do not want empty hypotheses
          if (hypothesesPart === '') {
            continue;
          }

          // Check if it is part of the previous hypothesis.
          if (hypothesesPart.startsWith('   ') || prevEndWithColon) {
            prevEndWithColon = false;
            hypotheses[hypotheses.length - 1].type =
              hypotheses[hypotheses.length - 1].type
                  .concat(' ' + hypothesesPart.trim());
            continue;
          }

          // If it is a new hypothesis, define the new hypothesis by
          // a term and its type
          const declarationIndex = hypothesesPart.indexOf(':');
          prevEndWithColon = hypothesesPart.trim().endsWith(':');
          hypotheses.push({
            terms: hypothesesPart.substring(0, declarationIndex + 1).trim(),
            type: hypothesesPart.substring(declarationIndex + 1).trim(),
          });
        }
        return hypotheses;
        // return this.parts[0].trim().replace(/\n/g, '<br>');
      }
    },
    subGoal: function() {
      if (this.parts.length > 1) {
        let goalString = this.parts[1].trim().replace(/\n/g, '<br>');
        if (goalString.search(/<br> {31}/g) !== -1) {
          goalString = goalString.replace(/<br> {31}/g, '<br>     ');
        } else if (goalString.search(/<br> {2}/g) !== -1) {
          goalString = goalString.replace(/<br> {2}/g, '<br>     ');
        }
        return goalString;
      }
    },
    showHypotheses: function() {
      return this.$store.state.settings.goalStyle !== 'goal';
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

<style lang="scss">

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

  .goal-with-hypotheses {
    margin-top: 0.3em;
    margin-left: 1em;
    white-space: break-spaces;
  }

  .goal-target {
    margin-top: 0.3em;
    white-space: break-spaces;
  }
</style>
