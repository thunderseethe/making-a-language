set -e

rm -rf node_modules/lsp-base
npm i lsp-base
rm -rf dist
npm run build
rm /var/www/playground/*
cp dist/* /var/www/playground/

