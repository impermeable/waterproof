const path = require('path');

module.exports = {
  chainWebpack: (config) => {
    // config.plugins.delete('preload-index');
    // config.plugins.delete('prefetch-index');
    // config.plugins.delete('preload-editpage');
    // config.plugins.delete('prefetch-editpage');
    config.plugins.delete('hmr');
  },
  configureWebpack: {
    module: {
      rules: [{
        test: /\.scss$/,
        use: [
          'sass-loader',
          {
            loader: 'style-resources-loader',
            options: {
              patterns: [
                path.resolve(__dirname,
                    'src/assets/stylesheets/abstracts/*.scss'),
              ],
            },
          },
        ],
      }],
    },
  },
  pages: {
    index: {
      entry: 'src/index/main.js',
    },
    editpage: {
      entry: 'src/editpage/main.js',
    },
  },
  pluginOptions: {
    electronBuilder: {
      // Sandboxing interferes with running the app on the GitLab runners.
      mainProcessArgs: ['--no-sandbox'],
    },
  },
};
