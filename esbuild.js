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
    external: ['vscode', 'path', 'fs', 'os', 'child_process', 'stream'],
};

// Config for webview source code (to be run in a web-based context)
/** @type BuildOptions */
const webviewConfig = {
    ...baseConfig,
    target: 'es2020',
    format: 'esm',
    tsconfig: 'tsconfig.webview.json',
    entryPoints: ['./src/webview/check-result-view.tsx'],
    outfile: './out/check-result-view.js',
    loader: {
        '.ttf': 'copy', // use the file loader to handle .ttf files
    }
};

/** @type BuildOptions */
const webviewCurrentProofStepConfig = {
    ...baseConfig,
    target: 'es2020',
    format: 'esm',
    tsconfig: 'tsconfig.webview.json',
    entryPoints: ['./src/webview/current-proof-step/main.tsx'],
    outfile: './out/current-proof-step.js',
    loader: {
        '.ttf': 'copy', // use the file loader to handle .ttf files
    }
};

/** @type BuildOptions */
const webviewCoverageConfig = {
    ...baseConfig,
    target: 'es2020',
    format: 'esm',
    tsconfig: 'tsconfig.webview.json',
    entryPoints: ['./src/webview/coverage-view.tsx'],
    outfile: './out/coverageView.js',
    loader: {
        '.ttf': 'copy', // use the file loader to handle .ttf files
    }
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
            (await context({...webviewConfig, plugins: watchPlugin('webviewConfig')})).watch();
            (await context({
                ...webviewCurrentProofStepConfig,
                plugins: watchPlugin('webviewCurrentProofStepConfig')
            })).watch();
            (await context({
                ...webviewCoverageConfig,
                plugins: watchPlugin('webviewCoverageConfig')
            })).watch();
        } else {
            // Build extension
            await build(extensionConfig);
            await build(extensionBrowserConfig);
            await build(webviewConfig);
            await build(webviewCurrentProofStepConfig);
            await build(webviewCoverageConfig);
            console.log('build complete');
        }
    } catch (err) {
        process.stderr.write(err.stderr);
        process.exit(1);
    }
})();
