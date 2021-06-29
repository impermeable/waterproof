module.exports = {
  perFile: true,
  include: ['src/**/*.{js,vue,ts}'],
  reportDir: 'out/coverage',
  reporter: ['text', 'text-summary', 'html'],
  instrument: false,
  sourceMap: false,
  all: true,
  watermarks: {
    'lines': [60, 75],
    'functions': [60, 75],
    'branches': [60, 75],
    'statements': [60, 75],
  },
};
