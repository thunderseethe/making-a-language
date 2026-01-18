const { merge } = require('webpack-merge')
const common = require('./webpack.common');

module.exports = merge(common, {
  mode: 'production',
  devtool: 'source-map',
  output: {
    publicPath: 'https://thunderseethe.dev/making-a-language',
  },
  optimization: {
    usedExports: false,
  },
});
