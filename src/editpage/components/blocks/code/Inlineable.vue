<template>
    <span v-if="inline">
        <slot></slot>
    </span>
    <pre v-else>
        <slot></slot>
    </pre>
</template>

<script>
export default {
  name: 'Inlineable',
  props: {
    inline: Boolean,
  },
};
</script>
