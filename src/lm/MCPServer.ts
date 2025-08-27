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
import { JarFileSystemProvider } from '../JarFileSystemProvider';
import { getSpecFiles, mapTlcOutputLine, outChannel } from '../commands/checkModel';
import { runTlc } from '../tla2tools';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';
import { getDiagnostic } from '../main';
import { moduleSearchPaths } from '../paths';

export class MCPServer implements vscode.Disposable {

    private mcpServer: http.Server | undefined;
    private jarProvider: JarFileSystemProvider;
    private jarProviderDisposable: vscode.Disposable;

    constructor(port: number) {
        // Initialize JAR file system provider
        this.jarProvider = new JarFileSystemProvider();
        this.jarProviderDisposable = vscode.workspace.registerFileSystemProvider('jarfile', this.jarProvider, {
            isReadonly: true
        });

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

    private startServer(port: number): void {
        try {
            const app = express();
            app.use(express.json());

            const server = this.getServer();
            app.post('/mcp', async (req, res) => {
                try {
                    const transport: StreamableHTTPServerTransport = new StreamableHTTPServerTransport({
                        sessionIdGenerator: undefined,
                    });
                    res.on('close', () => {
                        console.log('Request closed');
                        transport.close();
                    });
                    await server.connect(transport);
                    await transport.handleRequest(req, res, req.body);
                } catch (error) {
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
                    `Failed to start TLA+ MCP server: ${
                        err instanceof Error ? err.message : String(err)
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
        this.jarProviderDisposable.dispose();
        this.jarProvider.dispose();
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
                    // Resolve relative path to absolute path
                    const absolutePath = this.resolveFilePath(fileName);

                    // Turn the file name into a vscode.Uri
                    const fileUri = vscode.Uri.file(absolutePath);

                    // Check if the file exists
                    if (!(await exists(absolutePath))) {
                        return {
                            content: [{
                                type: 'text',
                                text: `File ${absolutePath} does not exist on disk.`
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
                                text: `No errors found in the TLA+ specification ${absolutePath}.`
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
            { fileName: z.string().describe('The full path to the file containing the TLA+ module.') },
            async ({ fileName }: { fileName: string }) => {
                try {
                    // Resolve relative path to absolute path
                    const absolutePath = this.resolveFilePath(fileName);

                    // Turn the file name into a vscode.Uri
                    const fileUri = vscode.Uri.file(absolutePath);
                    if (!(await exists(absolutePath))) {
                        return {
                            content: [{
                                type: 'text',
                                text: `File ${absolutePath} does not exist on disk.`
                            }]
                        };
                    }

                    const document = await vscode.workspace.openTextDocument(fileUri);
                    const tdsp = new TLADocumentSymbolProvider(new TlaDocumentInfos());
                    const symbols =
                        await tdsp.provideDocumentSymbols(document, new vscode.CancellationTokenSource().token);

                    return {
                        content: [{
                            type: 'text',
                            text: `Document symbols for ${absolutePath}:\n${JSON.stringify(symbols, null, 2)}`
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

                                    // Use the JarFileSystemProvider to read directory contents
                                    const entries = await this.jarProvider.readDirectory(jarUri);
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
                const cfgFilePath = cfgFile ? this.resolveFilePath(cfgFile) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ? ['-cleanup', '-modelcheck', ...extraOpts] : ['-cleanup', '-modelcheck'];
                return this.runTLCInMCP(absolutePath, options, [], cfgFilePath);
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
                const cfgFilePath = cfgFile ? this.resolveFilePath(cfgFile) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ? ['-cleanup', '-simulate', ...extraOpts] : ['-cleanup', '-simulate'];
                return this.runTLCInMCP(absolutePath, options, ['-Dtlc2.TLC.stopAfter=3'], cfgFilePath);
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_explore',
            // eslint-disable-next-line max-len
            'Explore the given TLA+ module by using TLC to randomly generate and print a behavior—a sequence of states, where each state represents an assignment of values to the module’s variables. Choose a meaningful value for the behavior length N that is neither too small nor too large, based on your estimate of what constitutes an interesting behavior for this particular module.',
            {
                fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.'),
                cfgFile: z.string().optional().describe('Optional path to a custom TLC configuration file.'),
                // eslint-disable-next-line max-len
                extraOpts: z.array(z.string()).optional().describe('Optional array of additional command-line options to pass to TLC beyond [-simulate, -invlevel].'),
                behaviorLength: z.number().min(1).describe('The length of the behavior to generate.')
            },
            async ({ fileName, behaviorLength, cfgFile, extraOpts }) => {
                const absolutePath = this.resolveFilePath(fileName);
                const cfgFilePath = cfgFile ? this.resolveFilePath(cfgFile) : undefined;
                // Prepend the command line argument ['-modelcheck'] to extra opts.
                const options = extraOpts ?
                    ['-cleanup', '-simulate', '-invlevel', behaviorLength.toString(), ...extraOpts] :
                    ['-cleanup', '-simulate', '-invlevel', behaviorLength.toString()];
                return this.runTLCInMCP(
                    absolutePath,
                    options,
                    ['-Dtlc2.TLC.stopAfter=3'],
                    cfgFilePath
                );
            }
        );

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

                // Add event listeners to capture stdout and stderr
                procInfo.process.stdout?.on('data', stdoutHandler);
                procInfo.process.stderr?.on('data', stdoutHandler);

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
