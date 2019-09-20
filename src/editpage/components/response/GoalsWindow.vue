<template>
  <div class="goals-window">
    <div class="goals-header">
      <h3>What is given / what you still need to show</h3>
    </div>
    <div v-if="ready" class="goals">
      <Goal v-for="(goal, index) in coqGoals" class="subgoal"
            :goal="goal" :index="index" :key="'goal' + index"
            :total="coqGoals.length">
      </Goal>
      <span v-if="!coqGoals">
        No goals active.
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
  .goals-header {
    display: flex;
    flex-flow: row nowrap;
    justify-content: space-between;
    border-bottom: 1px black solid;
    height: 40px;
    background: $color-primary-light;
    color: $color-on-primary;
    padding-left: 5px;
  }

  .goals-window {
    flex-grow: 1;
    flex-basis: 50%;
    min-height: 100px;
    border-bottom: 1px solid $color-primary-light;
  }

  .goals {
    width: calc(100% - 5px);
    height: calc(100% - 40px);
    margin-right: 5px;
    margin-bottom: 10px;
    overflow-y: auto;
  }

  .goals>:first-child {
    padding-top: 1.2em;
  }

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
