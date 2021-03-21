const path = require('path');
const webpack = require('webpack');
const BundleAnalyzerPlugin = require('webpack-bundle-analyzer').BundleAnalyzerPlugin;

module.exports = [
  {
    entry: './src/index.js',
    mode: 'development',
    devtool: 'eval',
    output: {
      path: path.resolve(__dirname),
      filename: 'public/js/index.main.js'
    },
    // devtool: 'inline-nosources-cheap-source-map',
    module: {
      rules: [
        {test: /\.(js|jsx)$/, use: 'babel-loader', exclude: /node_modules/}
      ]
    }
  }
];