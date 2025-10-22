import { z } from 'zod';
import * as http from 'http';
import * as path from 'path';
import * as fs from 'fs';
import express from 'express';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import * as vscode from 'vscode';
import { exists } from '../common';
import { applyDCollection } from '../diagnostic';
import { TLADocumentSymbolProvider } from '../symbols/tlaSymbols';
import { parseSpec, transpilePlusCal } from '../commands/parseModule';
import { TlaDocumentInfos } from '../model/documentInfo';
import { JarFileSystemProviderHandle, acquireJarFileSystemProvider } from '../JarFileSystemProvider';
import { getSpecFiles, mapTlcOutputLine, outChannel } from '../commands/checkModel';
import { runTlc } from '../tla2tools';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';
import { getDiagnostic } from '../main';
import { moduleSearchPaths } from '../paths';

export class MCPServer implements vscode.Disposable {

    private mcpServer: http.Server | undefined;
    private jarProviderHandle: JarFileSystemProviderHandle;

    constructor(port: number) {
        // Initialize JAR file system provider
        this.jarProviderHandle = acquireJarFileSystemProvider();

        this.startServer(port);
    }

    /**
     * Gets the path to the knowledge base directory within the extension.
     */
    private getKnowledgeBasePath(): string {
        // Get the extension context to find the extension path
        const extension = vscode.extensions.getExtension('tlaplus.vscode-ide');
        if (!extension) {
            throw new Error('TLA+ extension not found');
        }

        // The knowledge base is in the resources/knowledgebase directory of the extension
        return path.join(extension.extensionPath, 'resources', 'knowledgebase');
    }

    /**
     * Resolves a potentially relative file path to an absolute path.
     * If the path is already absolute, returns it as-is.
     * If the path is relative, resolves it relative to the workspace root.
     */
    private resolveFilePath(fileName: string): string {
        if (path.isAbsolute(fileName)) {
            return fileName;
        }

        // Get the workspace root directory
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            // If no workspace is open, resolve relative to the current working directory
            return path.resolve(fileName);
        }

        // Resolve relative to the workspace root
        return path.resolve(workspaceFolder.uri.fsPath, fileName);
    }

    /**
     * Validates that the given absolute path is within the workspace.
     * Returns the validated path if valid, throws an error if not.
     * Uses path.relative() to prevent path traversal attacks.
     */
    private validateWorkspacePath(absolutePath: string): string {
        const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
        if (!workspaceFolder) {
            throw new Error('No workspace is open');
        }

        const workspaceRoot = workspaceFolder.uri.fsPath;

        const normalizedWorkspace = path.normalize(workspaceRoot);
        const normalizedPath = path.normalize(absolutePath);

        let resolvedWorkspace: string;
        try {
            resolvedWorkspace = this.resolveCanonicalPath(normalizedWorkspace, false);
        } catch (error) {
            const workspaceError = error instanceof Error ? error.message : String(error);
            throw new Error(
                `Access denied: Unable to resolve workspace root (${normalizedWorkspace}): ` +
                workspaceError
            );
        }

        let resolvedTarget = normalizedPath;
        try {
            resolvedTarget = this.resolveCanonicalPath(normalizedPath, true);
        } catch (error) {
            if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
                const parentDir = path.dirname(normalizedPath);
                const fileName = path.basename(normalizedPath);
                try {
                    const resolvedParent = this.resolveCanonicalPath(parentDir, false);
                    resolvedTarget = path.join(resolvedParent, fileName);
                } catch (innerError) {
                    const parentError = innerError instanceof Error ? innerError.message : String(innerError);
                    throw new Error(
                        `Access denied: Path ${absolutePath} is outside the workspace (cannot resolve ` +
                        `${parentDir}): ${parentError}`
                    );
                }
            } else {
                const targetError = error instanceof Error ? error.message : String(error);
                throw new Error(
                    `Access denied: Unable to resolve target path (${normalizedPath}): ` +
                    targetError
                );
            }
        }

        // Use path.relative() to get the relative path from workspace to target
        const relativePath = path.relative(resolvedWorkspace, resolvedTarget);

        // Check for path traversal attempts:
        // 1. If relative path starts with '..' or contains '../' at the beginning, it's outside workspace
        // 2. If relative path is empty, it's the workspace root itself (allowed)
        // 3. On Windows, check for drive letter changes (e.g., C: to D:)
        if (relativePath.startsWith('..') || relativePath.startsWith(`..${path.sep}`)) {
            throw new Error(
                `Access denied: Path ${absolutePath} is outside the workspace (path traversal detected)`
            );
        }

        // Additional check for absolute paths that might bypass the relative check
        // This handles cases where the path might be on a different drive on Windows
        if (path.isAbsolute(relativePath)) {
            throw new Error(
                `Access denied: Path ${absolutePath} is outside the workspace (absolute path detected)`
            );
        }

        if (path.parse(resolvedWorkspace).root.toLowerCase() !== path.parse(resolvedTarget).root.toLowerCase()) {
            throw new Error(
                `Access denied: Path ${absolutePath} is outside the workspace (different volume)`
            );
        }

        return resolvedTarget;
    }

    private resolveCanonicalPath(absolutePath: string, allowMissing: boolean): string {
        const normalizedAbsolute = path.resolve(absolutePath);
        const parsed = path.parse(normalizedAbsolute);
        const baseRoot = parsed.root;
        const parts = normalizedAbsolute
            .slice(baseRoot.length)
            .split(path.sep)
            .filter(part => part.length > 0);

        let resolved = baseRoot;
        const realpathFn: (path: string) => string =
            typeof fs.realpathSync.native === 'function' ? fs.realpathSync.native : fs.realpathSync;

        for (let index = 0; index < parts.length; index += 1) {
            const segment = parts[index];
            const candidate = path.join(resolved, segment);

            try {
                resolved = realpathFn(candidate);
            } catch (error) {
                const err = error as NodeJS.ErrnoException;
                if (err.code === 'ENOENT' && allowMissing) {
                    resolved = candidate;
                    for (let rest = index + 1; rest < parts.length; rest += 1) {
                        resolved = path.join(resolved, parts[rest]);
                    }
                    return resolved;
                }
                throw err;
            }
        }

        return resolved;
    }

    private startServer(port: number): void {
        try {
            const app = express();
            app.use(express.json());

            app.post('/mcp', async (req, res) => {
                let serverInstance: McpServer | undefined;
                try {
                    serverInstance = this.getServer();
                    // Check for duplicate protocol version headers which cause LiteLLM to fail connecting.
                    const protocolVersion = req.headers['mcp-protocol-version'];
                    if (protocolVersion && typeof protocolVersion === 'string' && protocolVersion.includes(',')) {
                        // Normalize the protocol version by taking the first one
                        req.headers['mcp-protocol-version'] = protocolVersion.split(',')[0].trim();
                    }

                    const transport: StreamableHTTPServerTransport = new StreamableHTTPServerTransport({
                        sessionIdGenerator: undefined // Use stateless mode to avoid initialization complexity
                    });
                    res.on('close', () => {
                        console.log('Request closed');
                        transport.close();
                        if (serverInstance !== undefined) {
                            serverInstance.close().catch(error => {
                                console.warn('Error closing MCP server instance:', error);
                            });
                            serverInstance = undefined;
                        }
                    });
                    await serverInstance.connect(transport);
                    await transport.handleRequest(req, res, req.body);
                } catch (error) {
                    if (serverInstance !== undefined) {
                        serverInstance.close().catch(closeError => {
                            console.warn('Error closing MCP server instance after failure:', closeError);
                        });
                        serverInstance = undefined;
                    }
                    console.error('Error handling MCP request:', error);
                    if (!res.headersSent) {
                        res.status(500).json({
                            jsonrpc: '2.0',
                            error: {
                                code: -32603,
                                message: 'Internal server error',
                            },
                            id: null,
                        });
                    }
                }
            });

            // GET endpoint - return 405 for stateless mode
            // The server MUST either return Content-Type: text/event-stream in response to this HTTP GET,
            // or else return HTTP 405 Method Not Allowed, indicating that the server does not offer an
            // SSE stream at this endpoint.
            app.get('/mcp', (req, res) => {
                res.status(405).json({
                    jsonrpc: '2.0',
                    error: {
                        code: -32000,
                        message: 'Method not allowed.'
                    },
                    id: null
                });
            });

            // DELETE endpoint - return 405 for stateless mode
            // Clients that no longer need a particular session (e.g., because the user is leaving the client
            // application) SHOULD send an HTTP DELETE to the MCP endpoint with the Mcp-Session-Id header, to
            // explicitly terminate the session. The server MAY respond to this request with HTTP 405 Method
            // Not Allowed, indicating that the server does not allow clients to terminate sessions.
            app.delete('/mcp', (req, res) => {
                res.status(405).json({
                    jsonrpc: '2.0',
                    error: {
                        code: -32000,
                        message: 'Method not allowed.'
                    },
                    id: null
                });
            });


            this.mcpServer = app.listen(port, () => {
                // Get the actual port that was assigned (important when port is 0)
                const actualPort = (this.mcpServer?.address() as { port: number })?.port || port;
                console.log(`TLA+ MCP server listening at http://localhost:${actualPort}/mcp`);
                // Only show the information message if running in Cursor, not VSCode.
                const isCursor = vscode.env.appName?.toLowerCase().includes('cursor');
                if (isCursor) {
                    // Show an information message in Cursor including a button to add the MCP server to Cursor.
                    const addToCursor = 'Add to Cursor';
                    vscode.window.showInformationMessage(
                        `TLA+ MCP server listening at http://localhost:${actualPort}/mcp`,
                        addToCursor
                    ).then(opt => {
                        if (opt === addToCursor) {
                            // We will display the information message in Cursor regardless of whether the user has
                            // already added the MCP server.
                            // Fortunately, adding the MCP server is idempotent, so it can be safely repeated
                            // without causing issues.
                            vscode.workspace.getConfiguration().update(
                                'tlaplus.mcp.port',
                                actualPort,
                                vscode.ConfigurationTarget.Global
                            );
                            // base64 encode the URL
                            const CURSOR_CONFIG = JSON.stringify({
                                url: `http://localhost:${actualPort}/mcp`
                            });
                            // https://docs.cursor.com/deeplinks
                            // eslint-disable-next-line max-len
                            const CURSOR_DEEPLINK = `cursor://anysphere.cursor-deeplink/mcp/install?name=TLA+MCP+Server&config=${Buffer.from(CURSOR_CONFIG).toString('base64')}`;
                            console.log(`Cursor deeplink: ${CURSOR_DEEPLINK}`);
                            // Use the external URI handler to open the deeplink in Cursor because
                            // vscode.commands.executeCommand('vscode.open', CURSOR_DEEPLINK) doesn't work.
                            vscode.env.openExternal(vscode.Uri.parse(CURSOR_DEEPLINK));
                        }
                    });
                }
            }).on('error', (err) => {
                vscode.window.showErrorMessage(
                    `Failed to start TLA+ MCP server: ${err instanceof Error ? err.message : String(err)
                    }`
                );
                console.error('Error starting TLA+ MCP server:', err);
            });

        } catch (err) {
            // eslint-disable-next-line max-len
            vscode.window.showErrorMessage(`Failed to start TLA+ MCP server: ${err instanceof Error ? err.message : String(err)}`);
        }
    }

    public dispose(): void {
        if (this.mcpServer) {
            this.mcpServer.close();
            this.mcpServer = undefined;
        }

        // Clean up JAR file system provider
        this.jarProviderHandle.dispose();
    }

    private getServer(): McpServer {
        const server = new McpServer({
            name: 'TLA+ MCP Tools',
            version: '1.0.0',
        }, {
            capabilities: {
                resources: {}  // Enable resource support
            }
        });

        server.tool(
            'tlaplus_mcp_sany_parse',
            // eslint-disable-next-line max-len
            'Parse the input TLA+ module using SANY from the TLA+ tools. Use SANY to perform syntax and level-checking of the module. Ensure that the input is provided as a fully qualified file path, as required by the tool.',
            { fileName: z.string().describe('The full path to the file containing the TLA+ module.') },
            async ({ fileName }: { fileName: string }) => {
                try {
                    // Resolve relative path to absolute path and validate it's within workspace
                    const absolutePath = this.resolveFilePath(fileName);
                    const validatedPath = this.validateWorkspacePath(absolutePath);

                    // Turn the file name into a vscode.Uri
                    const fileUri = vscode.Uri.file(validatedPath);

                    // Check if the file exists
                    if (!(await exists(validatedPath))) {
                        return {
                            content: [{
                                type: 'text',
                                text: `File ${validatedPath} does not exist on disk.`
                            }]
                        };
                    }

                    // Transpile PlusCal to TLA+ (if any), and parse the resulting TLA+ spec
                    const messages = await transpilePlusCal(fileUri);
                    const specData = await parseSpec(fileUri);

                    // Post-process SANY's parse results
                    messages.addAll(specData.dCollection);
                    const diagnostic = getDiagnostic();
                    applyDCollection(messages, diagnostic);

                    // Format the result based on whether there were any errors
                    if (messages.messages.length === 0) {
                        return {
                            content: [{
                                type: 'text',
                                text: `No errors found in the TLA+ specification ${validatedPath}.`
                            }]
                        };
                    } else {
                        return {
                            content: messages.messages.map(msg => ({
                                type: 'text',
                                // eslint-disable-next-line max-len
                                text: `Parsing of file ${msg.filePath} failed at line ${msg.diagnostic.range.start.line + 1} with error: '${msg.diagnostic.message}'`
                            }))
                        };
                    }
                } catch (error) {
                    return {
                        content: [{
                            type: 'text',
                            // eslint-disable-next-line max-len
                            text: `Error processing TLA+ specification: ${error instanceof Error ? error.message : String(error)}`
                        }]
                    };
                }
            }
        );

        server.tool(
            'tlaplus_mcp_sany_symbol',
            // eslint-disable-next-line max-len
            'Extract all symbols from the given TLA+ module. Use this tool to identify the symbols defined in a TLA+ specification—such as when generating a TLC configuration file. It assists in determining the list of CONSTANTS, the initialization predicate, the next-state relation, the overall behavior specification (Spec), and any defined safety or liveness properties. Note: SANY expects the fully qualified file path to the TLA+ module.',
            {
                fileName: z.string().describe(
                    'The full path to the file containing the TLA+ module ' +
                    '(including jarfile:... paths for modules inside JAR archives).'
                ),
                includeExtendedModules: z.boolean().optional().describe(
                    'If true, includes symbols from extended and instantiated modules. ' +
                    'By default, only symbols from the current module are included.'
                )
            },
            async ({ fileName, includeExtendedModules }: { fileName: string; includeExtendedModules?: boolean }) => {
                try {
                    let fileUri: vscode.Uri;
                    let displayPath: string;

                    // Check if this is a JAR file path
                    if (fileName.startsWith('jarfile:')) {
                        // Use the jarfile URI directly
                        fileUri = vscode.Uri.parse(fileName);
                        displayPath = fileName;
                    } else {
                        // Regular file system path
                        const absolutePath = this.resolveFilePath(fileName);
                        const validatedPath = this.validateWorkspacePath(absolutePath);
                        fileUri = vscode.Uri.file(validatedPath);
                        displayPath = validatedPath;

                        // Check if file exists on disk
                        if (!(await exists(validatedPath))) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `File ${validatedPath} does not exist on disk.`
                                }]
                            };
                        }
                    }

                    const document = await vscode.workspace.openTextDocument(fileUri);
                    const tdsp = new TLADocumentSymbolProvider(new TlaDocumentInfos());
                    const symbols =
                        await tdsp.provideDocumentSymbols(
                            document, new vscode.CancellationTokenSource().token, includeExtendedModules
                        );

                    return {
                        content: [{
                            type: 'text',
                            text: `Document symbols for ${displayPath}:\n${JSON.stringify(symbols, null, 2)}`
                        }]
                    };
                } catch (error) {
                    return {
                        content: [{
                            type: 'text',
                            // eslint-disable-next-line max-len
                            text: `Failed to retrieve document symbols: ${error instanceof Error ? error.message : String(error)}`
                        }]
                    };
                }
            }
        );

        server.tool(
            'tlaplus_mcp_sany_modules',
            // eslint-disable-next-line max-len
            'Retrieves a list of all TLA+ modules recognized by SANY, making it easy to see which modules can be imported into a TLA+ specification.',
            {},
            async () => {
                try {
                    const sources = moduleSearchPaths.getSources();
                    const modulesBySearchPath: { [searchPath: string]: string[] } = {};

                    for (const source of sources) {
                        const paths = moduleSearchPaths.getSourcePaths(source.name);

                        for (const searchPath of paths) {
                            // if searchPath starts with jarfile:/path/to/file.jar, list the
                            // *.tla files contained in the jar file using JarFileSystemProvider
                            if (searchPath.startsWith('jarfile:')) {
                                try {
                                    // Convert searchPath to a proper jarfile URI
                                    const jarUri = vscode.Uri.parse(searchPath);

                                    // Use the workspace FS (backed by the shared jarfile provider) to enumerate entries
                                    const entries = await vscode.workspace.fs.readDirectory(jarUri);
                                    const tlaFiles = entries
                                        .filter(([name, type]) =>
                                            type === vscode.FileType.File && name.endsWith('.tla'))
                                        .map(([name]) => name);

                                    if (tlaFiles.length > 0) {
                                        modulesBySearchPath[searchPath] = [];
                                        for (const file of tlaFiles) {
                                            const moduleName = path.basename(file);
                                            // Skip modules whose name starts with '_'
                                            if (!moduleName.startsWith('_')) {
                                                const s = `${searchPath}${path.sep}${moduleName}`;
                                                modulesBySearchPath[searchPath].push(s);
                                            }
                                        }
                                    }
                                } catch (error) {
                                    // Log error but continue processing other search paths
                                    console.warn(`Failed to read JAR directory ${searchPath}: ${error}`);
                                }
                            } else if (await exists(searchPath)) {
                                const files = await fs.promises.readdir(searchPath);
                                const tlaFiles = files.filter(file => file.endsWith('.tla'));

                                if (tlaFiles.length > 0) {
                                    modulesBySearchPath[searchPath] = [];
                                    for (const file of tlaFiles) {
                                        // Skip modules whose name starts with '_'
                                        const moduleName = path.basename(file, '.tla');
                                        if (!moduleName.startsWith('_')) {
                                            // prefix with searchPath (use platform-specific path separator)
                                            modulesBySearchPath[searchPath].push(`${searchPath}${path.sep}${file}`);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Format output grouped by search path
                    const output: string[] = [];
                    for (const [searchPath, modules] of Object.entries(modulesBySearchPath)) {
                        output.push(`Search path: ${searchPath}`);
                        for (const module of modules) {
                            output.push(`  ${module}`);
                        }
                        output.push(''); // Add empty line between groups
                    }

                    return {
                        content: [{
                            type: 'text',
                            text: `Available TLA+ modules from configured search paths:\n\n${output.join('\n')}`
                        }]
                    };
                } catch (error) {
                    return {
                        content: [{
                            type: 'text',
                            // eslint-disable-next-line max-len
                            text: `Failed to retrieve list of modules: ${error instanceof Error ? error.message : String(error)}`
                        }]
                    };
                }
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_check',
            // eslint-disable-next-line max-len
            'Perform an exhaustive model check of the TLA+ module provided as an input file using TLC. Model checking is a formal verification method that systematically explores all reachable states of a system to verify its correctness. This includes checking both safety and liveness properties, and identifying any counterexamples that violate the specified properties. Please note that TLC requires the fully qualified file path to the TLA+ module. Be aware that, due to the potential for state-space explosion, exhaustive model checking may be computationally intensive and time-consuming. In some cases, it may be infeasible to check very large models exhaustively.',
            {
                fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.'),
                cfgFile: z.string().optional().describe('Optional path to a custom TLC configuration file.'),
                // eslint-disable-next-line max-len
                extraOpts: z.array(z.string()).optional().describe('Optional array of additional command-line options to pass to TLC beyond [-modelcheck].')
            },
            async ({ fileName, cfgFile, extraOpts }) => {
                const absolutePath = this.resolveFilePath(fileName);
                const validatedPath = this.validateWorkspacePath(absolutePath);
                const cfgFilePath = cfgFile ? this.validateWorkspacePath(this.resolveFilePath(cfgFile)) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ? ['-cleanup', '-modelcheck', ...extraOpts] : ['-cleanup', '-modelcheck'];
                return this.runTLCInMCP(validatedPath, options, [], cfgFilePath);
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_smoke',
            // eslint-disable-next-line max-len
            'Smoke test the TLA+ module using TLC with the provided input file. Smoke testing is a lightweight verification technique that runs TLC in simulation mode to randomly explore as many behaviors as possible within a specified time limit. This method does not attempt to exhaustively explore the entire state space. If no counterexample is found, it does not imply that the module is correct—only that no violations were observed within the constraints of the test. If a counterexample is found, it demonstrates that the module violates at least one of its specified properties. Note that any counterexample produced may not be minimal due to the non-exhaustive nature of the search. TLC expects the fully qualified file path to the input module.',
            {
                fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.'),
                cfgFile: z.string().optional().describe('Optional path to a custom TLC configuration file.'),
                // eslint-disable-next-line max-len
                extraOpts: z.array(z.string()).optional().describe('Optional array of additional command-line options to pass to TLC beyond [-simulate].')
            },
            async ({ fileName, cfgFile, extraOpts }) => {
                const absolutePath = this.resolveFilePath(fileName);
                const validatedPath = this.validateWorkspacePath(absolutePath);
                const cfgFilePath = cfgFile ? this.validateWorkspacePath(this.resolveFilePath(cfgFile)) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ? ['-cleanup', '-simulate', ...extraOpts] : ['-cleanup', '-simulate'];
                return this.runTLCInMCP(validatedPath, options, ['-Dtlc2.TLC.stopAfter=3'], cfgFilePath);
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_explore',
            // eslint-disable-next-line max-len
            'Explore the given TLA+ module by using TLC to randomly generate and print a behavior—a sequence of states, where each state represents an assignment of values to the module\'s variables. Choose a meaningful value for the behavior length N that is neither too small nor too large, based on your estimate of what constitutes an interesting behavior for this particular module.',
            {
                fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.'),
                cfgFile: z.string().optional().describe('Optional path to a custom TLC configuration file.'),
                // eslint-disable-next-line max-len
                extraOpts: z.array(z.string()).optional().describe('Optional array of additional command-line options to pass to TLC beyond [-simulate, -invlevel].'),
                behaviorLength: z.number().min(1).describe('The length of the behavior to generate.')
            },
            async ({ fileName, behaviorLength, cfgFile, extraOpts }) => {
                const absolutePath = this.resolveFilePath(fileName);
                const validatedPath = this.validateWorkspacePath(absolutePath);
                const cfgFilePath = cfgFile ? this.validateWorkspacePath(this.resolveFilePath(cfgFile)) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ?
                    ['-cleanup', '-simulate', '-invlevel', behaviorLength.toString(), ...extraOpts] :
                    ['-cleanup', '-simulate', '-invlevel', behaviorLength.toString()];
                return this.runTLCInMCP(
                    validatedPath,
                    options,
                    ['-Dtlc2.TLC.stopAfter=3'],
                    cfgFilePath
                );
            }
        );

        /*
        *
        * Provide auxiliary tools to list, read, and write files within the workspace.
        * The TLA+ tools (SANY, TLC, …) rely on a filesystem-centric model, which blocks
        * many workflows. Making them filesystem-agnostic
        * (https://github.com/tlaplus/tlaplus/issues/719) is a major refactoring and not
        * expected soon.
        *
        * Cursor and similar environments already provide filesystem operations, and those
        * should be preferred. Our filesystem tools exist as a fallback to avoid dead ends
        * when LLMs need to create files consumed by SANY, TLC, and related MCP tools.
        *
        * Clients could implement their own filesystem operations, but if client and server
        * run on different hosts, they would be unable to create files on the server host
        * where SANY/TLC run.
        *
        * Implementor's Notes:
        * - We chose to keep the TLA+ MCP tools file-based, even though their APIs could have
        * been migrated to streams. The risk was unclear client behavior: MCP clients like
        * Cursor ultimately need to write to files, since human users expect to view and
        * manage those files directly.
        * - MCP tools were chosen over MCP resources: they are widely supported, better for
        * interactive use, and simpler for validation.
        * - Filesystem operations use absolute paths, since TLC and SANY require them. For
        * security, access is restricted to files under the active VSCode or Cursor workspace.
        */

        // Check if filesystem tools should be enabled
        const enableFilesystemTools =
            vscode.workspace.getConfiguration().get<boolean>('tlaplus.mcp.enableFilesystemTools', false);

        if (enableFilesystemTools) {
            server.tool(
                'list_directory',
                // eslint-disable-next-line max-len
                'List the contents of a directory within the workspace. Only directories within the VSCode workspace are accessible for security reasons.',
                {
                    // eslint-disable-next-line max-len
                    directoryPath: z.string().describe('The absolute path to the directory to list. Must be within the workspace.')
                },
                async ({ directoryPath }) => {
                    try {
                        // Resolve and validate the path
                        const absolutePath = this.resolveFilePath(directoryPath);
                        const validatedPath = this.validateWorkspacePath(absolutePath);

                        // Check if the directory exists
                        if (!(await exists(validatedPath))) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `Directory ${validatedPath} does not exist.`
                                }]
                            };
                        }

                        // Check if it's actually a directory
                        const stat = await fs.promises.stat(validatedPath);
                        if (!stat.isDirectory()) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `Path ${validatedPath} is not a directory.`
                                }]
                            };
                        }

                        // Read directory contents
                        const entries = await fs.promises.readdir(validatedPath, { withFileTypes: true });

                        // Collect entries
                        const directories: string[] = [];
                        const files: string[] = [];
                        const symlinks: string[] = [];

                        for (const entry of entries) {
                            if (entry.isDirectory()) {
                                directories.push(entry.name);
                            } else if (entry.isFile()) {
                                files.push(entry.name);
                            } else if (entry.isSymbolicLink()) {
                                symlinks.push(entry.name);
                            }
                        }

                        // Sort all arrays alphabetically
                        directories.sort((a, b) => a.localeCompare(b));
                        files.sort((a, b) => a.localeCompare(b));
                        symlinks.sort((a, b) => a.localeCompare(b));

                        // Return structured JSON with metadata and entries separated
                        const result = {
                            metadata: {
                                path: validatedPath,
                                totalEntries: entries.length,
                                directoryCount: directories.length,
                                fileCount: files.length,
                                symlinkCount: symlinks.length
                            },
                            entries: {
                                directories: directories,
                                files: files,
                                symlinks: symlinks
                            }
                        };

                        return {
                            content: [{
                                type: 'text',
                                text: JSON.stringify(result, null, 2)
                            }]
                        };
                    } catch (error) {
                        return {
                            content: [{
                                type: 'text',
                                // eslint-disable-next-line max-len
                                text: `Error listing directory: ${error instanceof Error ? error.message : String(error)}`
                            }]
                        };
                    }
                }
            );

            server.tool(
                'read_file',
                // eslint-disable-next-line max-len
                'Read the contents of a file within the workspace. Only files within the VSCode workspace are accessible for security reasons.',
                {
                    // eslint-disable-next-line max-len
                    fileName: z.string().describe('The absolute path to the file to read. Must be within the VSCode or Cursor workspace.'),
                    // eslint-disable-next-line max-len
                    encoding: z.string().optional().describe('The encoding to use when reading the file. Defaults to utf-8.')
                },
                async ({ fileName, encoding = 'utf-8' }) => {
                    try {
                        // Resolve and validate the path
                        const absolutePath = this.resolveFilePath(fileName);
                        const validatedPath = this.validateWorkspacePath(absolutePath);

                        // Check if the file exists
                        if (!(await exists(validatedPath))) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `File ${validatedPath} does not exist.`
                                }]
                            };
                        }

                        // Check if it's actually a file
                        const stat = await fs.promises.stat(validatedPath);
                        if (!stat.isFile()) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `Path ${validatedPath} is not a file.`
                                }]
                            };
                        }

                        // Check file size to prevent reading very large files
                        const maxFileSize = 10 * 1024 * 1024; // 10MB limit
                        if (stat.size > maxFileSize) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `File ${validatedPath} is too large (${stat.size} bytes). ` +
                                        `Maximum allowed size is ${maxFileSize} bytes.`
                                }]
                            };
                        }

                        // Read the file contents
                        const fileContent = await fs.promises.readFile(
                            validatedPath,
                            { encoding: encoding as BufferEncoding }
                        );

                        // Return structured JSON with metadata and content separated
                        const result = {
                            metadata: {
                                path: validatedPath,
                                size: stat.size,
                                encoding: encoding,
                                mtime: stat.mtime.toISOString(),
                                ctime: stat.ctime.toISOString()
                            },
                            content: fileContent
                        };

                        return {
                            content: [{
                                type: 'text',
                                text: JSON.stringify(result, null, 2)
                            }]
                        };
                    } catch (error) {
                        return {
                            content: [{
                                type: 'text',
                                text: `Error reading file: ${error instanceof Error ? error.message : String(error)}`
                            }]
                        };
                    }
                }
            );

            server.tool(
                'write_file',
                // eslint-disable-next-line max-len
                'Write content to a file within the workspace. Only files within the VSCode workspace can be written for security reasons. Creates the file if it does not exist, or overwrites it if it does.',
                {
                    // eslint-disable-next-line max-len
                    fileName: z.string().describe('The absolute path to the file to write. Must be within the workspace.'),
                    // eslint-disable-next-line max-len
                    content: z.string().describe('The content to write to the file.'),
                    // eslint-disable-next-line max-len
                    encoding: z.string().optional().describe('The encoding to use when writing the file. Defaults to utf-8.'),
                    // eslint-disable-next-line max-len
                    createDirectories: z.boolean().optional().describe('Whether to create parent directories if they do not exist. Defaults to false.')
                },
                async ({ fileName, content, encoding = 'utf-8', createDirectories = false }) => {
                    try {
                        // Resolve and validate the path
                        const absolutePath = this.resolveFilePath(fileName);
                        const validatedPath = this.validateWorkspacePath(absolutePath);

                        // Check if parent directory exists, create if requested
                        const parentDir = path.dirname(validatedPath);
                        if (!(await exists(parentDir))) {
                            if (createDirectories) {
                                await fs.promises.mkdir(parentDir, { recursive: true });
                            } else {
                                return {
                                    content: [{
                                        type: 'text',
                                        text: `Parent directory ${parentDir} does not exist. ` +
                                            'Set createDirectories to true to create it automatically.'
                                    }]
                                };
                            }
                        }

                        // Check if the target is a directory
                        if (await exists(validatedPath)) {
                            const stat = await fs.promises.stat(validatedPath);
                            if (stat.isDirectory()) {
                                return {
                                    content: [{
                                        type: 'text',
                                        text: `Path ${validatedPath} is a directory, not a file.`
                                    }]
                                };
                            }
                        }

                        // Check content size to prevent writing very large files
                        const maxContentSize = 10 * 1024 * 1024; // 10MB limit
                        const contentBuffer = Buffer.from(content, encoding as BufferEncoding);
                        if (contentBuffer.length > maxContentSize) {
                            return {
                                content: [{
                                    type: 'text',
                                    text: `Content is too large (${contentBuffer.length} bytes). ` +
                                        `Maximum allowed size is ${maxContentSize} bytes.`
                                }]
                            };
                        }

                        // Write the file
                        await fs.promises.writeFile(validatedPath, content, { encoding: encoding as BufferEncoding });

                        // Get file stats after writing
                        const stat = await fs.promises.stat(validatedPath);

                        // Return structured JSON with operation result
                        const result = {
                            metadata: {
                                path: validatedPath,
                                size: stat.size,
                                encoding: encoding,
                                mtime: stat.mtime.toISOString(),
                                ctime: stat.ctime.toISOString(),
                                operation: 'write'
                            },
                            success: true,
                            message: `Successfully wrote ${stat.size} bytes to ${validatedPath}`
                        };

                        return {
                            content: [{
                                type: 'text',
                                text: JSON.stringify(result, null, 2)
                            }]
                        };
                    } catch (error) {
                        return {
                            content: [{
                                type: 'text',
                                text: `Error writing file: ${error instanceof Error ? error.message : String(error)}`
                            }]
                        };
                    }
                }
            );
        }

        // Register TLA+ knowledge base resources
        this.registerKnowledgeBaseResources(server);

        return server;
    }

    /**
     * Registers TLA+ knowledge base resources from the extension's knowledge base directory.
     */
    private registerKnowledgeBaseResources(server: McpServer): void {
        try {
            const knowledgeBasePath = this.getKnowledgeBasePath();

            // Check if the knowledge base directory exists
            if (!fs.existsSync(knowledgeBasePath)) {
                console.warn(`Knowledge base directory not found: ${knowledgeBasePath}`);
                return;
            }

            // Read all markdown files in the knowledge base directory
            const files = fs.readdirSync(knowledgeBasePath);
            const markdownFiles = files.filter(file => file.endsWith('.md'));

            // Register each markdown file as a resource
            for (const file of markdownFiles) {
                const filePath = path.join(knowledgeBasePath, file);
                const resourceName = path.basename(file); // keep .md extension to enable syntax highlighting in VSCode.
                const resourceUri = `tlaplus://knowledge/${resourceName}`;

                // The parsing logic below is simple and does not handle errors. This is acceptable because knowledge
                // base articles are version-controlled in Git, so we can assume they are properly formatted.

                // Read the frontmatter to get metadata
                const content = fs.readFileSync(filePath, 'utf-8');
                const lines = content.split('\n');
                let title = resourceName.replace(/-/g, ' ');
                let description = '';

                // Simple frontmatter parsing
                if (lines[0] === '---') {
                    let i = 1;
                    while (i < lines.length && lines[i] !== '---') {
                        const line = lines[i].trim();
                        if (line.startsWith('title:')) {
                            title = line.substring(6).trim();
                        } else if (line.startsWith('description:')) {
                            description = line.substring(12).trim();
                        }
                        i++;
                    }
                }

                // Register the resource
                server.resource(
                    resourceName,
                    resourceUri,
                    {
                        title: title,
                        description: description,
                        mimeType: 'text/markdown',
                        annotations: {
                            audience: ['user', 'assistant'],
                            priority: 0.8
                        }
                    },
                    async () => {
                        try {
                            const fileContent = await fs.promises.readFile(filePath, 'utf-8');
                            // Remove the frontmatter
                            const contentWithoutFrontmatter = fileContent.split('---').slice(2).join('---').trim();
                            return {
                                contents: [
                                    {
                                        uri: resourceUri,
                                        name: file,
                                        title: description, // Description as the title because it provides more context
                                        mimeType: 'text/markdown',
                                        text: contentWithoutFrontmatter
                                    }
                                ]
                            };
                        } catch (error) {
                            throw new Error(`Failed to read knowledge base file: ${error}`);
                        }
                    }
                );

                console.log(`Registered TLA+ knowledge base resource: ${resourceName} at ${resourceUri}`);
            }
        } catch (error) {
            console.error('Error registering knowledge base resources:', error);
        }
    }

    private async runTLCInMCP(
        fileName: string,
        extraOps: string[],
        extraJavaOpts: string[] = [],
        cfgFilePath?: string
    ): Promise<{
        content: { type: 'text'; text: string; }[];
    }> {
        // Create a URI from the file name
        const fileUri = vscode.Uri.file(fileName);
        // Check if the file exists
        if (!(await exists(fileName))) {
            return {
                content: [{
                    type: 'text',
                    text: `File ${fileName} does not exist on disk.`
                }]
            };
        }

        try {
            const specFiles = await getSpecFiles(fileUri, false);
            if (!specFiles) {
                // Extract the spec name from the file name.
                const specName = path.basename(fileName, path.extname(fileName));
                return {
                    content: [{
                        type: 'text',
                        // eslint-disable-next-line max-len
                        text: `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${fileName}. Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC guidelines.`
                    }]
                };
            }

            // Run TLC with the specified mode
            const shareStats = vscode.workspace.getConfiguration().get<ShareOption>(CFG_TLC_STATISTICS_TYPE);
            if (shareStats !== ShareOption.DoNotShare) {
                extraJavaOpts.push('-Dtlc2.TLC.ide=TLAiVSCode');
                // Wait for the statistics to be reported. Normally, TLC exits too quickly for this to happen,
                // which is intentional when TLC is run by humans. However, when invoked by the MCP server,
                // we want to ensure the statistics are reported, since the runtime is dominated by the LLM
                // invocation anyway.
                // https://github.com/tlaplus/tlaplus/commit/4c54d983415fcdce254be9a7e074175a200dda37
                extraJavaOpts.push('-Dutil.ExecutionStatisticsCollector.waitForCompletion=true');
            }

            // Use the provided cfgFilePath or default to specFiles.cfgFilePath
            const configFilePath = cfgFilePath || specFiles.cfgFilePath;

            const procInfo = await runTlc(
                specFiles.tlaFilePath, path.basename(configFilePath), false, extraOps, extraJavaOpts);
            if (procInfo === undefined) {
                return {
                    content: [{
                        type: 'text',
                        text: 'Failed to start TLC process'
                    }]
                };
            }

            // Bind to output channel for display in VS Code output view
            outChannel.bindTo(procInfo);

            // Use a proper promise to wait for process completion
            return await new Promise<{
                content: { type: 'text'; text: string; }[];
            }>(resolve => {
                // Create output collector
                const outputLines: string[] = [];

                // Custom handler for capturing output
                const stdoutHandler = (data: Buffer) => {
                    const str = data.toString();
                    const lines = str.split('\n');
                    for (const line of lines) {
                        if (line.trim() !== '') {
                            const cleanedLine = mapTlcOutputLine(line);
                            if (cleanedLine !== undefined) {
                                outputLines.push(cleanedLine);
                            }
                        }
                    }
                };

                // Add event listener to capture merged output
                procInfo.mergedOutput.on('data', stdoutHandler);

                // Listen for process completion
                procInfo.process.on('close', (code) => {
                    resolve({
                        content: [{
                            type: 'text',
                            text: `Model check completed with exit code ${code}.\n\n` +
                                `Output:\n${outputLines.join('\n')}`
                        }]
                    });
                });
            });
        } catch (error) {
            return {
                content: [{
                    type: 'text',
                    text: `Error running TLC: ${error instanceof Error ? error.message : String(error)}`
                }]
            };
        }
    }
}
