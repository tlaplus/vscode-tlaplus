import { promises as fs } from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { XMLParser } from 'fast-xml-parser';
import { runXMLExporter } from '../tla2tools';

export interface ModuleReferences {
    extends?: Set<string>;
    instances?: Set<string>;
}

/**
    Extracts module references from a model file.
    - EXTENDS clauses are read from the source text to avoid false positives when SANY
      cannot load missing modules.
    - INSTANCE references come from SANY's XML exporter so we rely on the real parser
      rather than string matching.
 */
export async function getModuleReferences(tlaUri: vscode.Uri): Promise<ModuleReferences | undefined> {
    const extendsModules = await readExtendsModules(tlaUri.fsPath);
    const instanceModules = await readInstanceModules(tlaUri);

    if (!extendsModules && !instanceModules) {
        return undefined;
    }

    return {
        extends: extendsModules,
        instances: instanceModules
    };
}

async function readInstanceModules(tlaUri: vscode.Uri): Promise<Set<string> | undefined> {
    try {
        const procInfo = await runXMLExporter(tlaUri, false, true);
        let stdout = '';
        procInfo.mergedOutput.on('data', chunk => {
            stdout += chunk.toString();
        });

        const exitCode = await new Promise<number>((resolve) => {
            procInfo.process.on('close', (code) => resolve(code ?? 1));
        });
        if (exitCode !== 0 || stdout.length === 0) {
            return undefined;
        }

        const parser = new XMLParser({
            ignoreAttributes: false,
            attributeNamePrefix: '',
            isArray: (name) => ['entry', 'InstanceNode', 'OpDeclNodeRef'].includes(name)
        });
        const xml = parser.parse(stdout);
        const entries = xml?.modules?.context?.entry as unknown[] | undefined;
        if (!entries || entries.length === 0) {
            return undefined;
        }

        const targetModule = path.basename(tlaUri.fsPath, '.tla');
        const instanceNames = new Set<string>();

        for (const entry of entries) {
            const moduleNode = (entry as Record<string, unknown>).ModuleNode as Record<string, unknown> | undefined;
            if (!moduleNode) {
                continue;
            }
            if (moduleNode.uniquename !== targetModule) {
                continue;
            }
            const instanceNode = moduleNode.InstanceNode;
            if (!instanceNode) {
                break;
            }
            const instances = Array.isArray(instanceNode) ? instanceNode : [instanceNode];
            for (const inst of instances) {
                const modName = (inst as Record<string, unknown>).module;
                if (typeof modName === 'string' && modName.trim().length > 0) {
                    instanceNames.add(modName.trim());
                }
            }
            break;
        }

        return instanceNames;
    } catch (err) {
        console.warn(`Unable to read INSTANCE references for ${tlaUri.fsPath}: ${err}`);
        return undefined;
    }
}

async function readExtendsModules(modelPath: string): Promise<Set<string> | undefined> {
    let text: string;
    try {
        text = await fs.readFile(modelPath, 'utf8');
    } catch (err) {
        console.warn(`Unable to read model file ${modelPath}: ${err}`);
        return undefined;
    }

    const lines = text.split(/\r?\n/);
    let inBlockComment = false;

    for (const line of lines) {
        let processed = '';
        let i = 0;
        while (i < line.length) {
            const ch = line[i];
            const next = line[i + 1];
            if (inBlockComment) {
                if (ch === '*' && next === ')') {
                    inBlockComment = false;
                    i += 2;
                    continue;
                }
                i += 1;
                continue;
            }
            if (ch === '(' && next === '*') {
                inBlockComment = true;
                i += 2;
                continue;
            }
            processed += ch;
            i += 1;
        }

        const leadingTrimmed = processed.trimStart();
        if (leadingTrimmed.startsWith('\\*')) {
            continue;
        }

        const inlineCommentPos = processed.indexOf('\\*');
        const withoutInlineComment = inlineCommentPos >= 0
            ? processed.slice(0, inlineCommentPos)
            : processed;

        const trimmed = withoutInlineComment.trim();
        if (trimmed.length === 0) {
            continue;
        }
        if (trimmed.startsWith('EXTENDS')) {
            const remainder = trimmed.substring('EXTENDS'.length).trim();
            if (remainder.length === 0) {
                return new Set();
            }
            const modules = remainder
                .split(',')
                .map(m => m.trim())
                .filter(m => m.length > 0);
            return new Set(modules);
        }
        if (trimmed.startsWith('VARIABLES') || trimmed.startsWith('VARIABLE') || trimmed.includes('==')) {
            break;
        }
    }
    return undefined;
}
