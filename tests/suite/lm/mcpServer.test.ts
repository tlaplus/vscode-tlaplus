import * as assert from 'assert';
import * as fs from 'fs';
import * as http from 'http';
import * as net from 'net';
import * as os from 'os';
import osModule from 'os';
import * as path from 'path';
import { ChildProcess } from 'child_process';
import { EventEmitter } from 'events';
import * as vscode from 'vscode';
import { MCPServer, advertisedHost, bindHost, hasIPv4Loopback } from '../../../src/lm/MCPServer';
import { McpServer as SdkMcpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import * as checkModel from '../../../src/commands/checkModel';
import * as common from '../../../src/common';
import * as tla2tools from '../../../src/tla2tools';
import { ToolProcessInfo } from '../../../src/tla2tools';
import { SpecFiles } from '../../../src/model/check';

const fsp = fs.promises;

class MockStdout extends EventEmitter {
    public on(event: string | symbol, listener: (...args: unknown[]) => void): this {
        return super.on(event, listener);
    }
}

class MockProcess extends EventEmitter {
    public stdout = new MockStdout();
    public stderr = new MockStdout();
    public killed = false;
    public exitCode: number | null = null;
    public signalCode: NodeJS.Signals | null = null;
    public pid = 99999;

    kill(signal?: NodeJS.Signals | number): boolean {
        this.killed = true;
        this.emit('killed', signal);
        return true;
    }
}

suite('MCP Server regressions', () => {
    suite('validateArticleName should prevent path traversal', () => {
        const prototype = MCPServer.prototype as unknown as {
            validateArticleName(name: string): void;
        };

        test('validateArticleName accepts valid article names', () => {
            const validNames = [
                'tla-choose-nondeterminism',
                'tla-diagnose-property-violations',
                'simple-article',
                'article_with_underscores',
                'Article123',
                'a',
                'article.md'
            ];

            for (const name of validNames) {
                assert.doesNotThrow(() => {
                    prototype.validateArticleName(name);
                }, `Should accept valid article name: ${name}`);
            }
        });

        test('validateArticleName rejects path traversal attempts', () => {
            const maliciousNames = [
                '../../../etc/passwd',
                '..\\..\\windows\\system32\\config\\sam',
                'article/../../../secret.txt',
                'article\\..\\..\\secret.txt',
                '../article',
                '..\\article',
                'article/subdir/file',
                'article\\subdir\\file'
            ];

            for (const name of maliciousNames) {
                assert.throws(() => {
                    prototype.validateArticleName(name);
                }, /Invalid article name.*contains path/, `Should reject malicious name: ${name}`);
            }
        });

        test('validateArticleName rejects dangerous characters', () => {
            const dangerousNames = [
                'article\x00null',  // null byte
                'article<script>',
                'article>redirect',
                'article|pipe',
                'article*wildcard',
                'article?query',
                'article"quote',
                'article\'quote',
                'article`backtick',
                'article;semicolon',
                'article:colon'
            ];

            for (const name of dangerousNames) {
                assert.throws(() => {
                    prototype.validateArticleName(name);
                }, /Invalid article name.*contains (invalid characters|null byte)/, `Should reject dangerous name: ${name}`);
            }
        });

        test('validateArticleName rejects empty and invalid inputs', () => {
            const invalidInputs = [
                '',
                null as unknown as string,
                undefined as unknown as string,
                123 as unknown as string,
                {} as unknown as string
            ];

            for (const input of invalidInputs) {
                assert.throws(() => {
                    prototype.validateArticleName(input);
                }, /Article name must be a non-empty string/, `Should reject invalid input: ${input}`);
            }
        });

        test('validateArticleName rejects excessively long names', () => {
            const longName = 'a'.repeat(101);
            assert.throws(() => {
                prototype.validateArticleName(longName);
            }, /Invalid article name.*is too long/, 'Should reject names longer than 100 characters');

            const maxLengthName = 'a'.repeat(100);
            assert.doesNotThrow(() => {
                prototype.validateArticleName(maxLengthName);
            }, 'Should accept names exactly 100 characters long');
        });
    });

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
                const boundHost = typeof address === 'object' && address !== null ? address.address : '127.0.0.1';

                const response = await new Promise<{ statusCode: number | undefined }>((resolve, reject) => {
                    const req = http.request({
                        hostname: boundHost,
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
                const boundHost = typeof address === 'object' && address !== null ? address.address : '127.0.0.1';

                const makePostRequest = async () => await new Promise<void>((resolve, reject) => {
                    const req = http.request({
                        hostname: boundHost,
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

    suite('Bind address', () => {
        const ipv6Loopback = {
            address: '::1', netmask: 'ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff', family: 'IPv6' as const,
            mac: '00:00:00:00:00:00', internal: true, cidr: '::1/128', scopeid: 0,
        };
        const ipv4Loopback = {
            address: '127.0.0.1', netmask: '255.0.0.0', family: 'IPv4' as const,
            mac: '00:00:00:00:00:00', internal: true, cidr: '127.0.0.1/8',
        };
        const ipv4Outside = {
            address: '192.0.2.5', netmask: '255.255.255.0', family: 'IPv4' as const,
            mac: '02:00:00:00:00:01', internal: false, cidr: '192.0.2.5/24',
        };
        const hasLoopbackIPv6 = () => Object.values(os.networkInterfaces())
            .flatMap((addresses) => addresses ?? [])
            .some((address) => address.internal && address.address === '::1');

        test('The HTTP server binds loopback', async function() {
            let server: MCPServer | undefined;
            try {
                server = new MCPServer(0);
                const httpServer = (server as unknown as {
                    mcpServer?: http.Server;
                }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');

                await new Promise<void>((resolve, reject) => {
                    httpServer.once('listening', () => resolve()).once('error', reject);
                });

                const address = httpServer.address();
                const host = typeof address === 'object' && address !== null ? address.address : address;
                assert.ok(host === '127.0.0.1' || host === '::1',
                    `The MCP server must bind loopback by default, not every interface: ${host}`);
            } finally {
                server?.dispose();
            }
        });

        test('The HTTP server binds the name localhost by default', async function() {
            // The name, not an address of one family, must reach the bind. With no IPv4 on loopback it becomes ::1.
            if (!hasIPv4Loopback()) {
                this.skip();
            }
            const prototype = net.Server.prototype as unknown as { listen: (...args: unknown[]) => net.Server };
            const originalListen = prototype.listen;
            const calls: Array<{ server: net.Server; host: unknown }> = [];
            let server: MCPServer | undefined;
            try {
                prototype.listen = function(this: net.Server, ...args: unknown[]) {
                    calls.push({ server: this, host: args[1] });
                    return originalListen.apply(this, args);
                };
                server = new MCPServer(0);
                const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                await new Promise<void>((resolve, reject) => {
                    httpServer.once('listening', () => resolve()).once('error', reject);
                });
                assert.deepStrictEqual(calls.filter((call) => call.server === httpServer).map((call) => call.host),
                    ['localhost'], 'The default must reach the bind as the name localhost, not as 127.0.0.1');
            } finally {
                prototype.listen = originalListen;
                server?.dispose();
            }
        });

        test('The HTTP server binds the host of the setting', async function() {
            // ::1, because the extension host resolves names IPv4 first, so localhost binds 127.0.0.1 there.
            if (!hasLoopbackIPv6()) {
                this.skip();
            }
            type Provider = { provideMcpServerDefinitions(token: unknown): Array<{ uri: vscode.Uri }> };
            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: Provider) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered = new Promise<Provider>((resolve) => {
                lm.registerMcpServerDefinitionProvider = (_id: string, provider: Provider) => {
                    resolve(provider);
                    return { dispose: () => undefined };
                };
            });
            const config = vscode.workspace.getConfiguration();
            let server: MCPServer | undefined;
            try {
                await config.update('tlaplus.mcp.host', '::1', vscode.ConfigurationTarget.Global);
                server = new MCPServer(0);
                const httpServer = (server as unknown as {
                    mcpServer?: http.Server;
                }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                const provider = await Promise.race([
                    registered,
                    new Promise<never>((_resolve, reject) => httpServer.once('error', reject)),
                ]);

                const address = httpServer.address();
                const host = typeof address === 'object' && address !== null ? address.address : address;
                assert.strictEqual(host, '::1', 'The MCP server must bind the host of tlaplus.mcp.host');
                // Also where loopback has IPv4, the URL must name the bound address, not a name.
                const url = provider.provideMcpServerDefinitions(undefined)[0].uri.toString(true);
                assert.strictEqual(new URL(url).hostname, '[::1]', `${url} must name [::1]`);
                const statusCode = await new Promise<number | undefined>((resolve, reject) => {
                    http.get(url, res => {
                        res.resume();
                        res.on('end', () => resolve(res.statusCode));
                    }).on('error', reject);
                });
                assert.strictEqual(statusCode, 405, `GET ${url} must reach the server`);
            } finally {
                server?.dispose();
                lm.registerMcpServerDefinitionProvider = originalRegister;
                await config.update('tlaplus.mcp.host', undefined, vscode.ConfigurationTarget.Global);
            }
        });

        test('A host outside loopback is kept', () => {
            // The setting may put the server on one interface or on every one, on purpose. No port is opened here.
            assert.strictEqual(bindHost('0.0.0.0', true), '0.0.0.0');
            assert.strictEqual(bindHost('192.0.2.7', true), '192.0.2.7');
        });

        test('A failed bind reports the error', async function() {
            const vscodeWindow = vscode.window as unknown as {
                showErrorMessage: (message: string) => Thenable<undefined>;
            };
            const originalShowErrorMessage = vscodeWindow.showErrorMessage;
            const reported: string[] = [];
            vscodeWindow.showErrorMessage = (message: string) => {
                reported.push(message);
                return Promise.resolve(undefined);
            };

            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: unknown) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered: string[] = [];
            lm.registerMcpServerDefinitionProvider = (id: string) => {
                registered.push(id);
                return { dispose: () => undefined };
            };

            // Another server holds the port on the loopback address that the default gives, so the bind fails.
            // 192.0.2.1 is an address for documentation, which the machine does not have, so that bind fails too.
            const holder = http.createServer();
            try {
                await new Promise<void>((resolve, reject) => {
                    holder.once('error', reject).listen(0, bindHost(undefined), () => resolve());
                });
                const address = holder.address();
                assert.ok(typeof address === 'object' && address !== null, 'The holder should bind a port');
                const failures: Array<[number, string, string]> = [
                    [address.port, address.address, 'EADDRINUSE'],
                    [0, '192.0.2.1', 'EADDRNOTAVAIL'],
                ];
                for (const [port, host, code] of failures) {
                    reported.length = 0;
                    const server = new MCPServer(port, host);
                    try {
                        const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                        assert.ok(httpServer, 'MCP HTTP server should be created');
                        // The error listeners run in order, so the error is reported before this one runs.
                        await new Promise<void>((resolve, reject) => {
                            httpServer.once('error', () => resolve())
                                .once('listening', () => reject(new Error(`The bind to ${host} should fail`)));
                        });
                        assert.strictEqual(reported.length, 1, `The failed bind to ${host} should be reported once`);
                        assert.ok(reported[0].startsWith('Failed to start TLA+ MCP server'), reported[0]);
                        assert.ok(reported[0].includes(code), reported[0]);
                    } finally {
                        server.dispose();
                    }
                }
                assert.deepStrictEqual(registered, [], 'A server that did not bind must not register a URL');
            } finally {
                holder.close();
                vscodeWindow.showErrorMessage = originalShowErrorMessage;
                lm.registerMcpServerDefinitionProvider = originalRegister;
            }
        });

        test('A host that is not a non-empty string binds loopback', async function() {
            // A setting can hold any JSON value, and VS Code returns it raw. Node binds every interface for a host that
            // is not a string, or is empty. Such a value must give the default host.
            const prototype = net.Server.prototype as unknown as { listen: (...args: unknown[]) => net.Server };
            const originalListen = prototype.listen;
            const calls: Array<{ server: net.Server; host: unknown }> = [];
            try {
                prototype.listen = function(this: net.Server, ...args: unknown[]) {
                    calls.push({ server: this, host: args[1] });
                    return originalListen.apply(this, args);
                };
                for (const value of [8080, true, { a: 1 }, ['127.0.0.1'], '']) {
                    await vscode.workspace.getConfiguration()
                        .update('tlaplus.mcp.host', value, vscode.ConfigurationTarget.Global);
                    // The default binds loopback too, so a setting that missed the value would pass.
                    assert.strictEqual(JSON.stringify(vscode.workspace.getConfiguration().get('tlaplus.mcp.host')),
                        JSON.stringify(value), 'tlaplus.mcp.host should hold the value written');
                    const server = new MCPServer(0);
                    try {
                        const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                        assert.ok(httpServer, 'MCP HTTP server should be created');
                        await new Promise<void>((resolve, reject) => {
                            httpServer.once('listening', () => resolve()).once('error', reject);
                        });
                        const hosts = calls.filter((call) => call.server === httpServer).map((call) => call.host);
                        assert.deepStrictEqual(hosts, [bindHost(undefined)],
                            `The setting ${JSON.stringify(value)} must bind the default host`);
                        const address = httpServer.address();
                        const host = typeof address === 'object' && address !== null ? address.address : address;
                        assert.ok(host === '127.0.0.1' || host === '::1',
                            `The setting ${JSON.stringify(value)} must bind loopback, not ${host}`);
                    } finally {
                        server.dispose();
                    }
                }
            } finally {
                prototype.listen = originalListen;
                await vscode.workspace.getConfiguration()
                    .update('tlaplus.mcp.host', undefined, vscode.ConfigurationTarget.Global);
            }
        });

        test('The URL registered with VS Code reaches the server', async function() {
            type Provider = { provideMcpServerDefinitions(token: unknown): Array<{ uri: vscode.Uri }> };
            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: Provider) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered = new Promise<Provider>((resolve) => {
                lm.registerMcpServerDefinitionProvider = (_id: string, provider: Provider) => {
                    resolve(provider);
                    return { dispose: () => undefined };
                };
            });

            let server: MCPServer | undefined;
            try {
                server = new MCPServer(0);
                const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                const provider = await Promise.race([
                    registered,
                    new Promise<never>((_resolve, reject) => httpServer.once('error', reject)),
                ]);
                const definitions = provider.provideMcpServerDefinitions(undefined);
                assert.strictEqual(definitions.length, 1, 'One server definition should be registered');
                const url = definitions[0].uri.toString(true);
                const bound = httpServer.address();
                assert.ok(typeof bound === 'object' && bound !== null, 'The HTTP server should be bound');
                assert.strictEqual(new URL(url).hostname.replace(/^\[(.*)\]$/, '$1'), bound.address,
                    `${url} must name the bound address`);
                const statusCode = await new Promise<number | undefined>((resolve, reject) => {
                    http.get(url, res => {
                        res.resume();
                        res.on('end', () => resolve(res.statusCode));
                    }).on('error', reject);
                });
                assert.strictEqual(statusCode, 405, `GET ${url} must reach the server`);
            } finally {
                server?.dispose();
                lm.registerMcpServerDefinitionProvider = originalRegister;
            }
        });

        test('With no IPv4 on loopback, the server binds ::1 and registers [::1]', async function() {
            // The interface list says loopback has ::1 alone. The server must bind ::1 and advertise [::1].
            if (!hasLoopbackIPv6()) {
                this.skip();
            }
            type Provider = { provideMcpServerDefinitions(token: unknown): Array<{ uri: vscode.Uri }> };
            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: Provider) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered = new Promise<Provider>((resolve) => {
                lm.registerMcpServerDefinitionProvider = (_id: string, provider: Provider) => {
                    resolve(provider);
                    return { dispose: () => undefined };
                };
            });
            const nodeOs = osModule as unknown as { networkInterfaces: () => NodeJS.Dict<os.NetworkInterfaceInfo[]> };
            const originalInterfaces = nodeOs.networkInterfaces;

            let server: MCPServer | undefined;
            try {
                nodeOs.networkInterfaces = () => ({ lo: [ipv6Loopback] });
                server = new MCPServer(0);
                const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                const provider = await Promise.race([
                    registered,
                    new Promise<never>((_resolve, reject) => httpServer.once('error', reject)),
                ]);
                const bound = httpServer.address();
                assert.ok(typeof bound === 'object' && bound !== null, 'The HTTP server should be bound');
                assert.strictEqual(bound.address, '::1', 'With no IPv4 on loopback, localhost must bind ::1');
                const url = provider.provideMcpServerDefinitions(undefined)[0].uri.toString(true);
                assert.strictEqual(new URL(url).hostname, '[::1]', `${url} must name [::1]`);
                const statusCode = await new Promise<number | undefined>((resolve, reject) => {
                    http.get(url, res => {
                        res.resume();
                        res.on('end', () => resolve(res.statusCode));
                    }).on('error', reject);
                });
                assert.strictEqual(statusCode, 405, `GET ${url} must reach the server`);
            } finally {
                nodeOs.networkInterfaces = originalInterfaces;
                server?.dispose();
                lm.registerMcpServerDefinitionProvider = originalRegister;
            }
        });

        test('The URL of a bind to :: names 127.0.0.1 where loopback has IPv4', async function() {
            // A bind to :: would put the server on the network. So the server binds 127.0.0.1, and the code that
            // builds the URL is told that the bound address is ::.
            if (!hasIPv4Loopback()) {
                this.skip();
            }
            type Provider = { provideMcpServerDefinitions(token: unknown): Array<{ uri: vscode.Uri }> };
            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: Provider) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered = new Promise<Provider>((resolve) => {
                lm.registerMcpServerDefinitionProvider = (_id: string, provider: Provider) => {
                    resolve(provider);
                    return { dispose: () => undefined };
                };
            });

            let server: MCPServer | undefined;
            try {
                server = new MCPServer(0, '127.0.0.1');
                const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                const boundAddress = httpServer.address.bind(httpServer);
                httpServer.address = () => {
                    const bound = boundAddress();
                    return typeof bound === 'object' && bound !== null
                        ? { ...bound, address: '::', family: 'IPv6' } : bound;
                };
                const provider = await Promise.race([
                    registered,
                    new Promise<never>((_resolve, reject) => httpServer.once('error', reject)),
                ]);
                const url = provider.provideMcpServerDefinitions(undefined)[0].uri.toString(true);
                assert.strictEqual(new URL(url).hostname, '127.0.0.1', `${url} must name 127.0.0.1`);
                const statusCode = await new Promise<number | undefined>((resolve, reject) => {
                    http.get(url, res => {
                        res.resume();
                        res.on('end', () => resolve(res.statusCode));
                    }).on('error', reject);
                });
                assert.strictEqual(statusCode, 405, `GET ${url} must reach the server`);
            } finally {
                server?.dispose();
                lm.registerMcpServerDefinitionProvider = originalRegister;
            }
        });

        test('The URL of a bind to :: names [::1] where loopback has no IPv4', async function() {
            // The interface list says loopback has ::1 alone. The server binds ::1, and the code that builds the URL
            // is told that the bound address is ::.
            if (!hasLoopbackIPv6()) {
                this.skip();
            }
            type Provider = { provideMcpServerDefinitions(token: unknown): Array<{ uri: vscode.Uri }> };
            const lm = vscode.lm as unknown as {
                registerMcpServerDefinitionProvider: (id: string, provider: Provider) => vscode.Disposable;
            };
            const originalRegister = lm.registerMcpServerDefinitionProvider;
            const registered = new Promise<Provider>((resolve) => {
                lm.registerMcpServerDefinitionProvider = (_id: string, provider: Provider) => {
                    resolve(provider);
                    return { dispose: () => undefined };
                };
            });
            const nodeOs = osModule as unknown as { networkInterfaces: () => NodeJS.Dict<os.NetworkInterfaceInfo[]> };
            const originalInterfaces = nodeOs.networkInterfaces;

            let server: MCPServer | undefined;
            try {
                nodeOs.networkInterfaces = () => ({ lo: [ipv6Loopback] });
                server = new MCPServer(0, '::1');
                const httpServer = (server as unknown as { mcpServer?: http.Server }).mcpServer;
                assert.ok(httpServer, 'MCP HTTP server should be created');
                const boundAddress = httpServer.address.bind(httpServer);
                httpServer.address = () => {
                    const bound = boundAddress();
                    return typeof bound === 'object' && bound !== null
                        ? { ...bound, address: '::', family: 'IPv6' } : bound;
                };
                const provider = await Promise.race([
                    registered,
                    new Promise<never>((_resolve, reject) => httpServer.once('error', reject)),
                ]);
                const url = provider.provideMcpServerDefinitions(undefined)[0].uri.toString(true);
                assert.strictEqual(new URL(url).hostname, '[::1]', `${url} must name [::1]`);
                const statusCode = await new Promise<number | undefined>((resolve, reject) => {
                    http.get(url, res => {
                        res.resume();
                        res.on('end', () => resolve(res.statusCode));
                    }).on('error', reject);
                });
                assert.strictEqual(statusCode, 405, `GET ${url} must reach the server`);
            } finally {
                nodeOs.networkInterfaces = originalInterfaces;
                server?.dispose();
                lm.registerMcpServerDefinitionProvider = originalRegister;
            }
        });

        test('The host setting defaults to localhost', () => {
            const extension = vscode.extensions.getExtension('tlaplus.vscode-ide');
            assert.ok(extension, 'The extension under test should be installed');
            const setting = extension.packageJSON.contributes.configuration.properties['tlaplus.mcp.host'];
            assert.ok(setting, 'package.json should declare tlaplus.mcp.host');
            assert.strictEqual(setting.default, 'localhost');
        });

        test('Only user or remote settings can set the host', () => {
            const extension = vscode.extensions.getExtension('tlaplus.vscode-ide');
            assert.ok(extension, 'The extension under test should be installed');
            const setting = extension.packageJSON.contributes.configuration.properties['tlaplus.mcp.host'];
            assert.ok(setting, 'package.json should declare tlaplus.mcp.host');
            assert.strictEqual(setting.scope, 'machine', 'A workspace must not change the bind address');
            // VS Code drops a machine setting from the settings of a workspace or folder, with no hint at run time.
            const instruction = 'Set it in the user settings of a local window, or in the remote settings of a remote '
                + 'window: VS Code ignores a value in the settings of a workspace or folder, such as '
                + '`.vscode/settings.json`.';
            assert.ok(String(setting.markdownDescription).includes(instruction),
                'The description must say where the value has to go');
        });

        test('The advertised URL names the bound address, or loopback for a wildcard bind', () => {
            const cases: Array<[string, string, string]> = [
                ['127.0.0.1', 'IPv4', '127.0.0.1'],
                ['::1', 'IPv6', '[::1]'],
                ['0.0.0.0', 'IPv4', '127.0.0.1'],
                ['::', 'IPv6', '127.0.0.1'],
                ['192.0.2.7', 'IPv4', '192.0.2.7'],
                ['2001:db8::7', 'IPv6', '[2001:db8::7]'],
            ];
            // On a loopback with IPv4, as on most machines.
            for (const [address, family, expected] of cases) {
                assert.strictEqual(advertisedHost({ address, family, port: 1 }, true), expected,
                    `advertised host for a bind to ${address}`);
            }
        });

        test('Only the loopback decides whether it has IPv4', () => {
            assert.strictEqual(hasIPv4Loopback(() => ({ lo: [ipv6Loopback] })), false);
            assert.strictEqual(hasIPv4Loopback(() => ({ lo: [ipv4Loopback] })), true, 'A loopback with IPv4 alone');
            assert.strictEqual(hasIPv4Loopback(() => ({ lo: [ipv6Loopback], eth0: [ipv4Outside] })), false,
                'An IPv4 address outside loopback does not count');
            assert.strictEqual(hasIPv4Loopback(() => ({ lo0: [ipv6Loopback, ipv4Loopback] })), true,
                'The loopback counts whatever its name');
            assert.strictEqual(hasIPv4Loopback(() => ({ lo0: [ipv6Loopback] })), false,
                'A loopback with no IPv4 counts whatever its name');
            assert.strictEqual(hasIPv4Loopback(() => ({})), true, 'A machine that lists no loopback keeps localhost');
            assert.strictEqual(hasIPv4Loopback(() => ({ eth0: [ipv4Outside] })), true,
                'Only the loopback is read: an IPv4 address outside it is no loopback');
        });

        test('localhost becomes ::1 when loopback has no IPv4', () => {
            assert.strictEqual(bindHost(undefined, false), '::1');
            assert.strictEqual(bindHost('localhost', false), '::1');
            assert.strictEqual(bindHost('LocalHost.', false), '::1');
            assert.strictEqual(bindHost('127.0.0.1', false), '127.0.0.1', 'An explicit address is kept');
            assert.strictEqual(bindHost(undefined, true), 'localhost');
        });

        test('A bind to :: is advertised as [::1] when loopback has no IPv4', () => {
            assert.strictEqual(advertisedHost({ address: '::', family: 'IPv6', port: 1 }, false), '[::1]');
        });

        test('An interface list that cannot be read keeps localhost', () => {
            const unreadable = (): NodeJS.Dict<os.NetworkInterfaceInfo[]> => {
                throw new Error('uv_interface_addresses failed');
            };
            assert.strictEqual(hasIPv4Loopback(unreadable), true);
            assert.strictEqual(bindHost(undefined, hasIPv4Loopback(unreadable)), 'localhost');
        });
    });

    suite('runTLCInMCP respects explicit cfgFile parameter', () => {
        let tmpDir: string;

        const getPrototype = () => MCPServer.prototype as unknown as {
            runTLCInMCP(
                fileName: string,
                extraOps: string[],
                extraJavaOpts: string[],
                cfgFilePath?: string
            ): Promise<{ content: { type: 'text'; text: string }[] }>;
        };

        setup(async () => {
            tmpDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'mcp-cfg-test-'));
        });

        teardown(async () => {
            await fsp.rm(tmpDir, { recursive: true, force: true });
        });

        test('returns config-not-found error when no cfgFile and no convention match', async function () {
            this.timeout(10000);
            const tlaFile = path.join(tmpDir, 'MySpec.tla');
            await fsp.writeFile(tlaFile, '---- MODULE MySpec ----\n====');

            const result = await getPrototype().runTLCInMCP.call({}, tlaFile, ['-simulate'], []);

            assert.ok(
                result.content[0].text.includes('Please create an MC'),
                'Should return config-not-found error when no cfgFile provided'
            );
        });

        test('bypasses config discovery when cfgFile is explicitly provided', async function () {
            this.timeout(10000);
            const tlaFile = path.join(tmpDir, 'MySpec.tla');
            const cfgFile = path.join(tmpDir, 'custom-scenario.cfg');
            await fsp.writeFile(tlaFile, '---- MODULE MySpec ----\n====');
            await fsp.writeFile(cfgFile, 'SPECIFICATION Spec');

            const result = await getPrototype().runTLCInMCP.call({}, tlaFile, ['-simulate'], [], cfgFile);
            const text = result.content[0].text;

            assert.ok(
                !text.includes('Please create an MC'),
                `Should not return config-not-found error when cfgFile is provided, got: ${text}`
            );
        });

        // Reproducer for the original bug: multiple .cfg files per module
        // with names that don't follow the {Spec}.cfg / MC{Spec}.cfg convention.
        // Before the fix, cfgFile was ignored and the tool returned
        // "No MySpec.cfg or MCMySpec.tla/MCMySpec.cfg files found" for every config.
        test('multiple cfg files per module — cfgFile selects the right config', async function () {
            this.timeout(10000);
            const tlaFile = path.join(tmpDir, 'MySpec.tla');
            await fsp.writeFile(tlaFile, '---- MODULE MySpec ----\n====');

            const configs = [
                'MySpec_positive.cfg',
                'MySpec_negative.cfg',
                'MySpec_bounded.cfg',
            ];
            for (const name of configs) {
                await fsp.writeFile(path.join(tmpDir, name), 'SPECIFICATION Spec');
            }

            for (const name of configs) {
                const cfgFile = path.join(tmpDir, name);
                const result = await getPrototype().runTLCInMCP.call(
                    {}, tlaFile, ['-simulate'], [], cfgFile
                );
                const text = result.content[0].text;
                assert.ok(
                    !text.includes('Please create an MC'),
                    `cfgFile=${name} should not trigger config-not-found error, got: ${text}`
                );
            }
        });

        test('returns clear error when explicit cfgFile does not exist', async function () {
            this.timeout(10000);
            const tlaFile = path.join(tmpDir, 'MySpec.tla');
            const cfgFile = path.join(tmpDir, 'nonexistent.cfg');
            await fsp.writeFile(tlaFile, '---- MODULE MySpec ----\n====');

            const result = await getPrototype().runTLCInMCP.call({}, tlaFile, ['-simulate'], [], cfgFile);
            const text = result.content[0].text;

            assert.ok(
                text.includes('does not exist on disk'),
                `Should return missing-file error for nonexistent cfgFile, got: ${text}`
            );
            assert.ok(
                text.includes('nonexistent.cfg'),
                `Error should mention the config file path, got: ${text}`
            );
        });
    });

    // Long-running TLC runs invoked through the MCP server (e.g.
    // `tlaplus_mcp_tlc_check` on a non-trivial spec) failed in Cursor with
    // `{"error":"fetch failed"}` after roughly a minute. MCP clients using
    // Streamable HTTP wrap each tool call in a single fetch() against the
    // SSE response stream; if the server stays silent for too long the
    // client aborts the underlying socket even though TLC is still
    // model checking. The fix is a periodic notifications/message ping on
    // the SSE stream, which is enough activity to keep the client's fetch
    // open. This suite pins down both halves of that contract: the timer
    // must actually fire while TLC is running, and it must be cleared
    // once the run finishes so we do not keep pinging a closed stream.
    suite('runTLCInMCP heartbeat keeps the MCP SSE stream alive', () => {
        type Notification = {
            method: string;
            params: { data?: unknown; level?: string; logger?: string };
        };

        const getPrototype = () => MCPServer.prototype as unknown as {
            runTLCInMCP(
                fileName: string,
                extraOps: string[],
                extraJavaOpts: string[],
                cfgFilePath?: string,
                toolExtra?: { sendNotification?: (n: Notification) => void | Promise<void> }
            ): Promise<{ content: { type: 'text'; text: string }[] }>;
        };

        type CheckModelMutable = {
            getSpecFiles: typeof checkModel.getSpecFiles;
            mapTlcOutputLine: typeof checkModel.mapTlcOutputLine;
            outChannel: typeof checkModel.outChannel;
        };
        type CommonMutable = { exists: typeof common.exists };
        type Tla2ToolsMutable = { runTlc: typeof tla2tools.runTlc };

        let originals: {
            getSpecFiles: typeof checkModel.getSpecFiles;
            mapTlcOutputLine: typeof checkModel.mapTlcOutputLine;
            bindTo: typeof checkModel.outChannel.bindTo;
            exists: typeof common.exists;
            runTlc: typeof tla2tools.runTlc;
        };
        let mockProcess: MockProcess;
        let runTlcCalls: number;

        setup(() => {
            const checkModelMutable = checkModel as unknown as CheckModelMutable;
            const commonMutable = common as unknown as CommonMutable;
            const tla2toolsMutable = tla2tools as unknown as Tla2ToolsMutable;

            originals = {
                getSpecFiles: checkModelMutable.getSpecFiles,
                mapTlcOutputLine: checkModelMutable.mapTlcOutputLine,
                bindTo: checkModelMutable.outChannel.bindTo,
                exists: commonMutable.exists,
                runTlc: tla2toolsMutable.runTlc
            };

            runTlcCalls = 0;
            mockProcess = new MockProcess();

            const specFiles = new SpecFiles(
                path.join(os.tmpdir(), 'HeartbeatExample.tla'),
                path.join(os.tmpdir(), 'HeartbeatExample.cfg')
            );

            checkModelMutable.getSpecFiles = async () => specFiles;
            checkModelMutable.mapTlcOutputLine = (line: string) => line.trim();
            checkModelMutable.outChannel.bindTo = () => { /* no-op */ };
            commonMutable.exists = async () => true;
            tla2toolsMutable.runTlc = async () => {
                runTlcCalls++;
                return new ToolProcessInfo('tlc', mockProcess as unknown as ChildProcess);
            };
        });

        teardown(() => {
            const checkModelMutable = checkModel as unknown as CheckModelMutable;
            const commonMutable = common as unknown as CommonMutable;
            const tla2toolsMutable = tla2tools as unknown as Tla2ToolsMutable;

            checkModelMutable.getSpecFiles = originals.getSpecFiles;
            checkModelMutable.mapTlcOutputLine = originals.mapTlcOutputLine;
            checkModelMutable.outChannel.bindTo = originals.bindTo;
            commonMutable.exists = originals.exists;
            tla2toolsMutable.runTlc = originals.runTlc;

            // Avoid leaking the parser awaiting a never-ending stream if a
            // test bailed out before emitting 'close'.
            if (mockProcess && mockProcess.listenerCount('close') > 0) {
                mockProcess.emit('close', 0);
            }
        });

        test('heartbeat fires repeatedly while TLC runs and stops once it ends', async function() {
            this.timeout(5000);

            const notifications: Notification[] = [];
            const sendNotification = (n: Notification) => {
                notifications.push(n);
            };

            // The production heartbeat interval is 10s. We only compress that
            // exact value so test code (mocha's own timeout, our wait loops,
            // ...) keeps using real wall-clock delays.
            const realSetInterval = global.setInterval;
            const HEARTBEAT_INTERVAL_MS = 10_000;
            const compressInterval = ((
                cb: (...args: unknown[]) => void,
                ms?: number,
                ...args: unknown[]
            ) => {
                const compressed = ms === HEARTBEAT_INTERVAL_MS ? 5 : ms;
                return realSetInterval(cb, compressed as number, ...args);
            }) as unknown as typeof setInterval;

            const heartbeatPings = () => notifications.filter(n =>
                n.method === 'notifications/message');

            global.setInterval = compressInterval;
            try {
                const tlaFile = path.join(os.tmpdir(), 'HeartbeatExample.tla');

                const runPromise = getPrototype().runTLCInMCP.call(
                    {},
                    tlaFile,
                    ['-cleanup', '-modelcheck'],
                    [],
                    undefined,
                    { sendNotification }
                );

                const deadline = Date.now() + 2000;
                while (heartbeatPings().length < 2 && Date.now() < deadline) {
                    await new Promise(resolve => setTimeout(resolve, 5));
                }

                const pingsWhileRunning = heartbeatPings().length;
                assert.ok(
                    pingsWhileRunning >= 2,
                    'Expected the heartbeat to fire repeatedly while TLC '
                        + `is running; saw ${pingsWhileRunning} ping(s). Without a `
                        + 'heartbeat MCP clients (e.g. Cursor) abort long-running '
                        + 'TLC tool calls with {"error":"fetch failed"}.'
                );

                for (const ping of heartbeatPings()) {
                    assert.strictEqual(
                        ping.method, 'notifications/message',
                        'Heartbeat must use notifications/message so it counts as '
                            + 'SSE traffic for MCP clients');
                    assert.strictEqual(
                        ping.params.level, 'debug',
                        'Heartbeat must use level=debug so MCP clients hide it from chat');
                    assert.strictEqual(
                        ping.params.logger, 'tlaplus_mcp_tlc',
                        'Heartbeat must be tagged with the TLC logger name');
                }

                // Close the process so runTLCInMCP resolves and clears the timer.
                mockProcess.emit('close', 0);
                await runPromise;
                const pingsAtClose = heartbeatPings().length;

                // If the timer leaked past 'close' we would keep pinging a
                // client that is no longer listening on the SSE stream.
                await new Promise(resolve => setTimeout(resolve, 80));
                assert.strictEqual(
                    heartbeatPings().length, pingsAtClose,
                    'Heartbeat timer must be cleared once the TLC run ends; '
                        + 'a leaked timer would keep pinging a closed SSE stream'
                );

                assert.strictEqual(runTlcCalls, 1, 'TLC should have been started exactly once');
            } finally {
                global.setInterval = realSetInterval;
            }
        });
    });
});
