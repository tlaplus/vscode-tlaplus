import { z } from 'zod';
import * as http from 'http';
import * as path from 'path';
import express from 'express';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import * as vscode from 'vscode';
import { LANG_TLAPLUS, exists } from '../common';
import { applyDCollection } from '../diagnostic';
import { TLADocumentSymbolProvider } from '../symbols/tlaSymbols';
import { parseSpec, transpilePlusCal } from '../commands/parseModule';
import { TlaDocumentInfos } from '../model/documentInfo';
import { getSpecFiles, mapTlcOutputLine, outChannel } from '../commands/checkModel';
import { runTlc } from '../tla2tools';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';

export class MCPServer implements vscode.Disposable {

    private mcpServer: http.Server | undefined;

    constructor(port: number) {
        this.startServer(port);
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
                vscode.window.showInformationMessage(`TLA+ MCP server listening at http://localhost:${port}/mcp`);
                console.log(`TLA+ MCP server listening at http://localhost:${port}/mcp`);
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
    }

    private getServer(): McpServer {
        const server = new McpServer({
            name: 'TLA+ MCP Tools',
            version: '1.0.0',
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
                    const diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
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
            'tlaplus_mcp_tlc_check',
            // eslint-disable-next-line max-len
            'Perform an exhaustive model check of the TLA+ module provided as an input file using TLC. Model checking is a formal verification method that systematically explores all reachable states of a system to verify its correctness. This includes checking both safety and liveness properties, and identifying any counterexamples that violate the specified properties. Please note that TLC requires the fully qualified file path to the TLA+ module. Be aware that, due to the potential for state-space explosion, exhaustive model checking may be computationally intensive and time-consuming. In some cases, it may be infeasible to check very large models exhaustively.',
            { fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.') },
            async ({ fileName }) => {
                const absolutePath = this.resolveFilePath(fileName);
                return this.runTLCInMCP(absolutePath, ['-modelcheck']);
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_smoke',
            // eslint-disable-next-line max-len
            'Smoke test the TLA+ module using TLC with the provided input file. Smoke testing is a lightweight verification technique that runs TLC in simulation mode to randomly explore as many behaviors as possible within a specified time limit. This method does not attempt to exhaustively explore the entire state space. If no counterexample is found, it does not imply that the module is correct—only that no violations were observed within the constraints of the test. If a counterexample is found, it demonstrates that the module violates at least one of its specified properties. Note that any counterexample produced may not be minimal due to the non-exhaustive nature of the search. TLC expects the fully qualified file path to the input module.',
            { fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.') },
            async ({ fileName }) => {
                const absolutePath = this.resolveFilePath(fileName);
                return this.runTLCInMCP(absolutePath, ['-simulate'], ['-Dtlc2.TLC.stopAfter=3']);
            }
        );

        server.tool(
            'tlaplus_mcp_tlc_explore',
            // eslint-disable-next-line max-len
            'Explore the given TLA+ module by using TLC to randomly generate and print a behavior—a sequence of states, where each state represents an assignment of values to the module’s variables. Choose a meaningful value for the behavior length N that is neither too small nor too large, based on your estimate of what constitutes an interesting behavior for this particular module.',
            { fileName: z.string().describe('The full path to the file containing the TLA+ module to parse.'), behaviorLength: z.number().min(1).describe('The length of the behavior to generate.') },
            async ({ fileName, behaviorLength }) => {
                const absolutePath = this.resolveFilePath(fileName);
                return this.runTLCInMCP(absolutePath, ['-simulate', '-invlevel', behaviorLength.toString()], ['-Dtlc2.TLC.stopAfter=3']);
            }
        );

        return server;
    }

    private async runTLCInMCP(fileName: string, extraOps: string[], extraJavaOpts: string[] = []): Promise<{
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

            const procInfo = await runTlc(
                specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath), false, extraOps, extraJavaOpts);
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
