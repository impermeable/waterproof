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
                    'src/assets/sass/abstracts/*.scss'),
              ],
            },
          },
        ],
      }],
    },
  },
  pluginOptions: {
    electronBuilder: {
      // Sandboxing interferes with running the app on the GitLab runners.
      mainProcessArgs: ['--no-sandbox'],
      nodeIntegration: true,
      builderOptions: {
        productName: 'Waterproof',
        remoteBuild: true,
        extraFiles: ['wrapper/assistance', 'wrapper/wplib'],
        publish: ['github'],
        win: {
          extraFiles: ['wrapper/win'],
        },
        mac: {
          extraFiles: ['wrapper/mac'],
        },
        linux: {
          extraFiles: ['wrapper/lin'],
          target: "AppImage",
        },
        fileAssociations: [
          {
            ext: 'wpn',
            name: 'Waterproof notebook',
          },
          {
            ext: 'wpe',
            name: 'Waterproof exercise',
          },
        ],
      },
    },
  },
};
