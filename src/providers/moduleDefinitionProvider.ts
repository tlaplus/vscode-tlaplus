import * as vscode from 'vscode';
import * as path from 'path';
import { JarModuleReader } from '../utils/jarReader';
import { moduleSearchPaths } from '../paths';

/**
 * Provides go-to-definition support for module names in EXTENDS statements.
 */
export class ModuleDefinitionProvider implements vscode.DefinitionProvider {
    private readonly jarReader: JarModuleReader;

    constructor(
        private readonly toolsJarPath: string,
        private readonly communityJarPath: string
    ) {
        this.jarReader = new JarModuleReader();
    }

    async provideDefinition(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken
    ): Promise<vscode.Definition | undefined> {
        // Get the word at the cursor position
        const wordRange = document.getWordRangeAtPosition(position, /[a-zA-Z_][a-zA-Z0-9_]*/);
        if (!wordRange) {
            return undefined;
        }

        const word = document.getText(wordRange);
        if (!word) {
            return undefined;
        }

        // Check if we're in an EXTENDS statement
        const line = document.lineAt(position.line).text;
        const beforeWord = line.substring(0, wordRange.start.character);

        // Look for EXTENDS on the current line or previous lines
        let inExtendsStatement = false;
        if (/EXTENDS\s*$/.test(beforeWord) || /EXTENDS\s+[\w\s,]*$/.test(beforeWord)) {
            inExtendsStatement = true;
        } else {
            // Check if we're on a continuation line of an EXTENDS statement
            for (let i = position.line - 1; i >= 0; i--) {
                const prevLine = document.lineAt(i).text;
                if (/EXTENDS\s+[\w\s,]*$/.test(prevLine)) {
                    // Check if there's no other statement between EXTENDS and current position
                    let hasOtherStatement = false;
                    for (let j = i + 1; j < position.line; j++) {
                        const checkLine = document.lineAt(j).text.trim();
                        if (checkLine && !checkLine.startsWith(',') && !/^[\w\s,]+$/.test(checkLine)) {
                            hasOtherStatement = true;
                            break;
                        }
                    }
                    if (!hasOtherStatement) {
                        inExtendsStatement = true;
                    }
                    break;
                }
                // Stop if we hit another statement
                if (prevLine.trim() && !/^[\w\s,]+$/.test(prevLine.trim())) {
                    break;
                }
            }
        }

        if (!inExtendsStatement) {
            return undefined;
        }

        // Try to find the module
        const moduleName = word;

        // 1. First, check workspace folders for local modules
        if (vscode.workspace.workspaceFolders) {
            for (const folder of vscode.workspace.workspaceFolders) {
                const moduleFile = path.join(folder.uri.fsPath, `${moduleName}.tla`);
                try {
                    const uri = vscode.Uri.file(moduleFile);
                    await vscode.workspace.fs.stat(uri);
                    return new vscode.Location(uri, new vscode.Position(0, 0));
                } catch {
                    // File doesn't exist, continue
                }
            }
        }

        // 2. Check module search paths from all sources
        const sources = moduleSearchPaths.getSources();
        for (const source of sources) {
            const paths = moduleSearchPaths.getSourcePaths(source.name);
            if (paths) {
                for (const searchPath of paths) {
                    const moduleFile = path.join(searchPath, `${moduleName}.tla`);
                    try {
                        const uri = vscode.Uri.file(moduleFile);
                        await vscode.workspace.fs.stat(uri);
                        return new vscode.Location(uri, new vscode.Position(0, 0));
                    } catch {
                        // File doesn't exist, continue
                    }
                }
            }
        }

        // 3. Check standard and community modules in JARs
        try {
            // Check standard modules
            const standardModules = await this.jarReader.listModules(this.toolsJarPath);
            const standardModule = standardModules.find(m => m.name === moduleName && m.category === 'standard');
            if (standardModule) {
                const uri = vscode.Uri.parse(`tla-module://standard/${moduleName}.tla`);
                return new vscode.Location(uri, new vscode.Position(0, 0));
            }

            // Check community modules
            const communityModules = await this.jarReader.listModules(this.communityJarPath);
            const communityModule = communityModules.find(m => m.name === moduleName && m.category === 'community');
            if (communityModule) {
                const uri = vscode.Uri.parse(`tla-module://community/${moduleName}.tla`);
                return new vscode.Location(uri, new vscode.Position(0, 0));
            }
        } catch (error) {
            console.error('Error searching for module in JARs:', error);
        }

        return undefined;
    }
}