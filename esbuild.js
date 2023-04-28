/* eslint-disable @typescript-eslint/no-var-requires */
/* eslint-disable no-undef */
const { build } = require('esbuild');

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
const extensionWebConfig = {
    ...baseConfig,
    platform: 'browser',
    format: 'cjs',
    entryPoints: ['./src/main.browser.ts'],
    outfile: './out/main.browser.js',
    external: ['vscode'],
};

// This watch config adheres to the conventions of the esbuild-problem-matchers
// extension (https://github.com/connor4312/esbuild-problem-matchers#esbuild-via-js)
/** @type BuildOptions */
const watchConfig = {
    watch: {
        onRebuild(error) {
            console.log('[watch] build started');
            if (error) {
                error.errors.forEach((error) =>
                    console.error(
                        `> ${error.location.file}:${error.location.line}:${error.location.column}: error: ${error.text}`
                    )
                );
            } else {
                console.log('[watch] build finished');
            }
        },
    },
};

// Build script
(async () => {
    try {
        if (args.includes('--watch')) {
            // Build and watch extension
            console.log('[watch] build started');
            await build({
                ...extensionConfig,
                ...watchConfig,
            });
            await build({
                ...extensionWebConfig,
                ...watchConfig,
            });
            console.log('[watch] build finished');
        } else {
            // Build extension
            await build(extensionConfig);
            await build(extensionWebConfig);
            console.log('build complete');
        }
    } catch (err) {
        process.stderr.write(err.stderr);
        process.exit(1);
    }
})();
