<template>
  <div class="goals-window">
    <div class="response-header">
      <h3>Proof progress</h3>
    </div>
    <div v-if="ready" class="goals">
      <Goal v-for="(goal, index) in coqGoals"
            :goal="goal" :index="index" :key="'goal' + index"
            :total="coqGoals.length">
      </Goal>
      <span v-if="!coqGoals.length">
        Done.
      </span>
    </div>
    <div style="text-align: center" v-else>
            <span>
                Loading Coq
            </span>
            <span class="load-dot" style="animation-delay: 0s">
                .
            </span>
            <span class="load-dot" style="animation-delay: 0.15s">
                .
            </span>
            <span class="load-dot" style="animation-delay: 0.3s">
                .
            </span>
        </div>
  </div>
</template>

<script>
import Goal from './Goal';

export default {
  name: 'GoalsWindow',
  props: ['goals', 'ready'],
  components: {
    Goal,
  },
  computed: {
    coqGoals: function() {
      return this.goals.split('\n\n').filter((goal) => goal !== '');
    },
  },
};
</script>

<style lang="scss" scoped>

  .load-dot {
      animation: 0.9s blink step-end infinite;
      color: black;
      margin-left: -4px;
  }

  @keyframes blink {
      from, to {
          color: transparent;
      }
      50% {
          color: black;
      }
  }
</style>
