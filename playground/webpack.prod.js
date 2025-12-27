const { merge } = require('webpack-merge')
const common = require('./webpack.common');

module.exports = merge(common, {
  mode: 'production',
  devtool: 'source-map',
  output: {
    publicPath: 'https://playground.thunderseethe.dev/',
  },
  optimization: {
    usedExports: false,
  },
});
