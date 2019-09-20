module.exports = {
  perFile: true,
  include: ['src/**/*.{js,vue}'],
  reportDir: 'out/coverage',
  reporter: ['text', 'text-summary', 'html'],
  instrument: false,
  sourceMap: false,
};
