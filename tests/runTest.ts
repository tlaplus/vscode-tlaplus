import { runTests } from '@vscode/test-electron';
import * as path from 'path';

async function main() {
    try {
        process.env.VSCODE_TEST = 'true';
        const extensionDevelopmentPath = path.resolve(__dirname, '../../');
        const extensionTestsPath = path.resolve(__dirname, './suite/index');
        await runTests({
            extensionDevelopmentPath,
            extensionTestsPath,
            launchArgs: ['--disable-extensions']
        });
    } catch (err) {
        console.error(`Failed to run tests: ${err}`);
        process.exit(1);
    }
}

main();
