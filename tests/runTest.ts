import { runTests } from '@vscode/test-electron';
import * as path from 'path';

async function main() {
    try {
        process.env.VSCODE_TEST = 'true';
        const extensionDevelopmentPath = path.resolve(__dirname, '../../');
        const extensionTestsPath = path.resolve(__dirname, './suite/index');
        const workspacePath = path.resolve(__dirname, './fixtures/workspaces/multi-root/multi-root.code-workspace');
        await runTests({
            extensionDevelopmentPath,
            extensionTestsPath,
            launchArgs: ['--disable-extensions', workspacePath]
        });
    } catch (err) {
        console.error(`Failed to run tests: ${err}`);
        process.exit(1);
    }
}

main();
