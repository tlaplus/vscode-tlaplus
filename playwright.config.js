const { defineConfig } = require('@playwright/test');

module.exports = defineConfig({
    testDir: './tests/playwright',
    timeout: 30000,
    use: {
        headless: true,
    },
    reporter: [['list']]
});
