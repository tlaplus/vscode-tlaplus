import * as assert from 'assert';
import * as fs from 'fs';
import * as http from 'http';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { MCPServer } from '../../../src/lm/MCPServer';
import { McpServer as SdkMcpServer } from '@modelcontextprotocol/sdk/server/mcp.js';

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

    suite('HTTP endpoint routing', () => {
        test('GET /mcp returns 405 without invoking the MCP handler', async function() {
            const prototype = MCPServer.prototype as unknown as {
                getServer(): unknown;
            };
            const originalGetServer = prototype.getServer;

            const connectCalls: unknown[] = [];
            prototype.getServer = () => ({
                async connect(transport: unknown) {
                    connectCalls.push(transport);
                }
            });

            let server: MCPServer | undefined;
            try {
                server = new MCPServer(0);
                const httpServer = (server as unknown as {
                    mcpServer?: http.Server;
                }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');

                await new Promise<void>((resolve) => {
                    httpServer.once('listening', () => resolve());
                });

                const address = httpServer.address();
                const port = typeof address === 'object' && address !== null ? address.port : address;
                assert.strictEqual(typeof port, 'number', 'HTTP server should expose a numeric port');

                const response = await new Promise<{ statusCode: number | undefined }>((resolve, reject) => {
                    const req = http.request({
                        hostname: '127.0.0.1',
                        port: port as number,
                        path: '/mcp',
                        method: 'GET'
                    }, res => {
                        res.resume();
                        res.on('end', () => resolve({ statusCode: res.statusCode }));
                    });
                    req.on('error', reject);
                    req.end();
                });

                assert.strictEqual(connectCalls.length, 0,
                    'GET /mcp should never reach the MCP request handler in stateless mode');
                assert.strictEqual(response.statusCode, 405,
                    'GET /mcp must return 405 when SSE is not supported');
            } finally {
                server?.dispose();
                prototype.getServer = originalGetServer;
            }
        });

        test('Each POST /mcp request uses a fresh MCP server instance', async function() {
            const prototype = MCPServer.prototype as unknown as {
                getServer(): unknown;
            };
            const originalGetServer = prototype.getServer;

            const serverInstances: SdkMcpServer[] = [];
            prototype.getServer = () => {
                const instance = new SdkMcpServer({
                    name: 'test-server',
                    version: '1.0.0'
                });
                serverInstances.push(instance);
                return instance;
            };

            let server: MCPServer | undefined;
            try {
                server = new MCPServer(0);
                const httpServer = (server as unknown as {
                    mcpServer?: http.Server;
                }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');

                await new Promise<void>((resolve) => {
                    httpServer.once('listening', () => resolve());
                });

                const address = httpServer.address();
                const port = typeof address === 'object' && address !== null ? address.port : address;
                assert.strictEqual(typeof port, 'number', 'HTTP server should expose a numeric port');

                const makePostRequest = async () => await new Promise<void>((resolve, reject) => {
                    const req = http.request({
                        hostname: '127.0.0.1',
                        port: port as number,
                        path: '/mcp',
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json',
                            'Accept': 'application/json, text/event-stream'
                        }
                    }, res => {
                        res.resume();
                        res.on('end', () => resolve());
                    });
                    req.on('error', reject);
                    req.write(JSON.stringify({
                        jsonrpc: '2.0',
                        id: 1,
                        method: 'ping'
                    }));
                    req.end();
                });

                await makePostRequest();
                await makePostRequest();

                assert.strictEqual(serverInstances.length, 2,
                    'Each POST /mcp request should create a fresh MCP server instance');
            } finally {
                await Promise.allSettled(serverInstances.map(instance => instance.close()));
                server?.dispose();
                prototype.getServer = originalGetServer;
            }
        });
    });
});
