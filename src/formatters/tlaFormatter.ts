import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { createHash } from 'crypto';
import { spawn } from 'child_process';
import { getJavaPath } from '../tla2tools';
import { moduleSearchPaths } from '../paths';

const CFG_FORMATTER_ENABLED = 'tlaplus.formatter.enabled';
const FORMATTER_JAR_NAME = 'tlaplus-formatter.jar';

/**
 * Builds `-DTLA-Library=...` with all module search paths (user-configured,
 * TLC standard/community modules, TLAPS) so the formatter's SANY can resolve
 * any EXTENDS'd modules. Paths using the `jarfile:` scheme are dropped because
 * Java's SANY resolves those from its own classpath.
 */
function makeFormatterTlaLibraryOpt(documentDir?: string): string {
    const allPaths: string[] = [];
    if (documentDir) {
        allPaths.push(documentDir);
    }
    for (const source of moduleSearchPaths.getSources()) {
        const sourcePaths = moduleSearchPaths.getSourcePaths(source.name);
        if (sourcePaths) {
            allPaths.push(...sourcePaths);
        }
    }
    const fsPaths = allPaths.filter(p => !p.startsWith('jar:') && !p.startsWith('jarfile:'));
    return '-DTLA-Library=' + fsPaths.join(path.delimiter);
}

export function extractModuleName(text: string): string | null {
    const regex = /^-{4,}\s*MODULE\s+(\w+)/m;
    const match = regex.exec(text);
    if (match && match[1]) {
        return match[1];
    }
    return null;
}

function generateHash(input: string, algorithm: string): string {
    const hash = createHash(algorithm);
    hash.update(input);
    return hash.digest('hex');
}

export function registerDocumentFormatter(context: vscode.ExtensionContext): void {
    const formatterJarPath = path.join(context.extensionPath, 'tools', FORMATTER_JAR_NAME);

    context.subscriptions.push(
        vscode.languages.registerDocumentFormattingEditProvider('tlaplus', {
            provideDocumentFormattingEdits(
                document: vscode.TextDocument
            ): vscode.ProviderResult<vscode.TextEdit[]> {
                const enabled = vscode.workspace.getConfiguration().get<boolean>(CFG_FORMATTER_ENABLED, true);
                if (!enabled) {
                    vscode.window.showInformationMessage(
                        'TLA+ formatter is disabled. Enable it via the "tlaplus.formatter.enabled" setting.'
                    );
                    return [];
                }

                return new Promise((resolve, reject) => {
                    const inputText = document.getText();
                    // The filename must match the module name for SANY to parse it.
                    // Prefer the on-disk filename; fall back to parsing the header.
                    const moduleName = (document.uri.scheme === 'file' && document.fileName.endsWith('.tla'))
                        ? path.basename(document.fileName, '.tla')
                        : extractModuleName(inputText);
                    if (!moduleName) {
                        vscode.window.showErrorMessage('Could not extract module name from the document.');
                        return resolve([]);
                    }

                    // Create a unique temp folder based on content hash.
                    const md5Hash = generateHash(inputText, 'md5');
                    const tempDir = path.join(context.globalStorageUri.fsPath, md5Hash);

                    try {
                        fs.mkdirSync(tempDir, { recursive: true });
                    } catch (err) {
                        if ((err as NodeJS.ErrnoException).code !== 'EEXIST') {
                            return reject(err);
                        }
                    }

                    const tempInputPath = path.join(tempDir, moduleName + '.tla');
                    const tempOutputPath = tempInputPath;
                    fs.writeFileSync(tempInputPath, inputText);

                    // Add the document's directory to the TLA-Library path so
                    // SANY can resolve EXTENDed modules relative to it.
                    const documentDir = document.uri.scheme === 'file'
                        ? path.dirname(document.uri.fsPath)
                        : undefined;

                    const javaPath = getJavaPath();
                    const stderrChunks: string[] = [];
                    const spawnArgs = [
                        makeFormatterTlaLibraryOpt(documentDir),
                        '-jar', formatterJarPath,
                        '-v', 'ERROR',
                        tempInputPath,
                        tempOutputPath
                    ];
                    const javaProcess = spawn(javaPath, spawnArgs);

                    javaProcess.stdout.on('data', (data) => {
                        console.log(`Formatter STDOUT: ${data}`);
                    });

                    javaProcess.stderr.on('data', (data) => {
                        stderrChunks.push(data.toString());
                        console.error(`Formatter STDERR: ${data}`);
                    });

                    javaProcess.on('error', (error) => {
                        vscode.window.showErrorMessage(`Formatter failed: ${error.message}`);
                        reject(error);
                    });

                    javaProcess.on('close', (code) => {
                        if (code !== 0) {
                            const stderr = stderrChunks.join('').trim();
                            const msg = stderr
                                ? `Formatter error: ${stderr}`
                                : `Formatter failed with exit code ${code}`;
                            vscode.window.showErrorMessage(msg);
                            fs.rmSync(tempDir, { recursive: true, force: true });
                            return reject(new Error(msg));
                        }
                        const formattedText = fs.readFileSync(tempOutputPath, 'utf8');
                        const edit = [vscode.TextEdit.replace(
                            new vscode.Range(0, 0, document.lineCount, 0),
                            formattedText
                        )];
                        fs.rmSync(tempDir, { recursive: true, force: true });
                        resolve(edit);
                    });
                });
            }
        })
    );
}
