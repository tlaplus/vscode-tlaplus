import * as path from 'path';

/**
 * Extracts the module name declared in a TLA+ module.
 */
export function extractModuleName(content: string): string | undefined {
    const headerRegex = /^\s*-{4,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{4,}/m;
    const match = headerRegex.exec(content);
    return match ? match[1] : undefined;
}

/**
 * Returns the set of modules referenced via EXTENDS or INSTANCE clauses.
 */
export function extractReferencedModuleNames(content: string): Set<string> {
    const sanitized = stripComments(content);
    const referenced = new Set<string>();

    // EXTENDS sections
    const extendsRegex = /\bEXTENDS\b([\s\S]*?)(?=\bVARIABLES\b|\bCONSTANTS\b|\bINSTANCE\b|\bLOCAL\b|\bRECURSIVE\b|\bASSUME\b|\bTHEOREM\b|\bLEMMA\b|\bAXIOM\b|\bFACT\b|\bPROOF\b|\bDEFINE\b|\bLET\b|\bMODULE\b|====|-{4,}|\w+\s*==|$)/gi;
    let match;
    while ((match = extendsRegex.exec(sanitized)) !== null) {
        const block = match[1];
        block.split(',')
            .map((token) => normalizeModuleReference(token))
            .forEach((name) => {
                if (name) {
                    referenced.add(name);
                }
            });
    }

    // INSTANCE clauses
    const instanceRegex = /\bINSTANCE\s+([A-Za-z0-9_']+)/gi;
    while ((match = instanceRegex.exec(sanitized)) !== null) {
        const name = normalizeModuleReference(match[1]);
        if (name) {
            referenced.add(name);
        }
    }

    return referenced;
}

/**
 * Removes comments from TLA+ module text.
 */
export function stripComments(text: string): string {
    return text
        .replace(/\(\*[\s\S]*?\*\)/g, ' ')
        .replace(/\\\*.*$/gm, '');
}

/**
 * Normalizes a module reference token by trimming whitespace and removing trailing ticks.
 */
export function normalizeModuleReference(token: string): string | undefined {
    const trimmed = token.trim();
    if (!trimmed) {
        return undefined;
    }
    const match = trimmed.match(/^([A-Za-z0-9_']+)/);
    if (!match) {
        return undefined;
    }
    return trimTrailingTicks(match[1]);
}

function trimTrailingTicks(name: string): string {
    return name.replace(/'+$/, '');
}

export function fallbackModuleNameFromPath(fsPath: string): string {
    const base = path.basename(fsPath, '.tla');
    return base;
}
