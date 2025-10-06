import * as assert from 'assert';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { MCPServer } from '../../../src/lm/MCPServer';

const fsp = fs.promises;

suite('MCP Server regressions', () => {
    suite('validateWorkspacePath should block symlinks', () => {
        test('validateWorkspacePath rejects escaped path', async function() {
            if (process.platform === 'win32') {
                this.skip();
            }

            const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
            if (!workspaceFolder) {
                this.skip();
            }

            const workspaceRoot = workspaceFolder.uri.fsPath;
            await fsp.mkdir(workspaceRoot, { recursive: true });
            const sandboxRoot = await fsp.mkdtemp(path.join(workspaceRoot, '.tmp-mcp-server-'));
            const outsideRoot = await fsp.mkdtemp(path.join(os.tmpdir(), 'mcp-server-outside-'));
            const secretPath = path.join(outsideRoot, 'secret.txt');

            try {
                await fsp.writeFile(secretPath, 'top secret');
                const linkPath = path.join(sandboxRoot, 'etc-link');
                try {
                    await fsp.symlink(outsideRoot, linkPath, 'dir');
                } catch (error) {
                    const code = (error as NodeJS.ErrnoException).code;
                    if (code === 'EPERM' || code === 'EACCES') {
                        this.skip();
                    }
                    throw error;
                }

                const prototype = MCPServer.prototype as unknown as {
                    validateWorkspacePath(p: string): string;
                    resolveCanonicalPath(p: string, allowMissing: boolean): string;
                };
                const helper = {
                    resolveCanonicalPath: prototype.resolveCanonicalPath
                };

                const escapedTarget = path.join(linkPath, 'secret.txt');

                try {
                    const result = prototype.validateWorkspacePath.call(helper, escapedTarget);
                    assert.fail(
                        `validateWorkspacePath accepted escaped path: ${result}`
                    );
                } catch (error) {
                    const message = error instanceof Error ? error.message : String(error);
                    assert.match(
                        message,
                        /Access denied/,
                        'validateWorkspacePath should reject symlink traversal outside the workspace'
                    );
                }
            } finally {
                await Promise.allSettled([
                    fsp.rm(sandboxRoot, { recursive: true, force: true }),
                    fsp.rm(outsideRoot, { recursive: true, force: true })
                ]);
            }
        });
    });
});
