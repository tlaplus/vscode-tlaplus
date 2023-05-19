/* eslint-disable @typescript-eslint/no-var-requires */
/* eslint-disable no-undef */
const { build, context } = require('esbuild');

//@ts-check
/** @typedef {import('esbuild').BuildOptions} BuildOptions **/

const args = process.argv.slice(2);

/** @type BuildOptions */
const baseConfig = {
    bundle: true,
    minify: args.includes('--production'),
    sourcemap: !args.includes('--production'),
};

// Config for extension source code (to be run in a Node-based context)
/** @type BuildOptions */
const extensionConfig = {
    ...baseConfig,
    platform: 'node',
    format: 'cjs',
    entryPoints: ['./src/main.ts'],
    outfile: './out/main.js',
    external: ['vscode'],
};

// Config for extension source code (to be run in a Web-based context)
/** @type BuildOptions */
const extensionBrowserConfig = {
    ...baseConfig,
    platform: 'browser',
    format: 'cjs',
    entryPoints: ['./src/main.browser.ts'],
    outfile: './out/main.browser.js',
    external: ['vscode'],
};

const watchPlugin = (name) => [{
    name: 'watch-plugin',
    setup(build) {
        build.onStart(() => console.log(`[watch] build started - ${name}`));
        build.onEnd(() => console.log(`[watch] build finished - ${name}`));
    },
}];

// Build script
(async () => {
    try {
        if (args.includes('--watch')) {
            // Build and watch extension
            (await context({...extensionConfig, plugins: watchPlugin('extensionConfig')})).watch();
            (await context({...extensionBrowserConfig, plugins: watchPlugin('extensionBrowserConfig')})).watch();
        } else {
            // Build extension
            await build(extensionConfig);
            await build(extensionBrowserConfig);
            console.log('build complete');
        }
    } catch (err) {
        process.stderr.write(err.stderr);
        process.exit(1);
    }
})();
