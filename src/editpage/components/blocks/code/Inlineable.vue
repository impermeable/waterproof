<template>
    <span v-if="inline">
        <slot />
    </span>
    <pre v-else>
        <slot />
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
