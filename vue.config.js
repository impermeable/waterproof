const path = require('path');

const bundleEnvName = 'WATERPROOF_BUILD_WITH_BUNDLED_INSTALLER';

let nsisConfig = undefined;
if (process.env[bundleEnvName] === 'true') {
  nsisConfig = {
    include: 'wrapper/windows-installer.nsh',
    allowElevation: true,
    oneClick: false,
    perMachine: true,
    artifactName: '${productName} and Coq Setup ${version}.${ext}',
  };
}

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
      // mainProcessArgs: ['--no-sandbox'],
      nodeIntegration: true,
      builderOptions: {
        productName: 'Waterproof',
        remoteBuild: true,
        extraFiles: ['wrapper/assistance', 'wrapper/wplib'],
        win: {
          extraFiles: ['wrapper/win'],
        },
        mac: {
          extraFiles: ['wrapper/mac'],
        },
        linux: {
          extraFiles: ['wrapper/lin'],
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
        nsis: nsisConfig,
      },
    },
  },
};
