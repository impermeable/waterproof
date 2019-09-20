if (process.env.NODE_ENV === 'coverage') {
  module.exports = {
    presets: ['@vue/app'],
    plugins: ['istanbul'],
  };
} else {
  module.exports = {
    presets: ['@vue/app'],
  };
}
