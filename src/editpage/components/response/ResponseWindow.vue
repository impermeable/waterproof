<template>
    <div class="response-window">
        <goals-window
                :goals="goals" :ready="ready">
        </goals-window>
        <messages-window
                :addError="addError" :ready="ready"
                :event-bus="eventBus">
        </messages-window>
    </div>
</template>

<script>
import GoalsWindow from './GoalsWindow';
import MessagesWindow from './MessagesWindow';

export default {
  name: 'ResponseWindow',
  components: {
    GoalsWindow,
    MessagesWindow,
  },
  props: {
    ready: Boolean,
    addError: Object,
    goals: String,
    eventBus: Object,
  },
};
</script>

<style lang="scss" scoped>
</style>
