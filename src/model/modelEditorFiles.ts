import * as path from 'path';

export type ModelBehaviorKind = 'initNext' | 'temporal' | 'none';
export type ConstantAssignmentKind = 'ordinary' | 'modelValue' | 'setModelValues';

export interface ModelEditorBehavior {
    kind: ModelBehaviorKind;
    init?: string;
    next?: string;
    temporal?: string;
}

export interface ModelEditorConstantAssignment {
    name: string;
    kind: ConstantAssignmentKind;
    value: string;
}

export interface DefinitionOverride {
    name: string;
    expression: string;
}

export interface ModelEditorState {
    specName: string;
    specPath: string;
    modelName: string;
    behavior: ModelEditorBehavior;
    checkDeadlock: boolean;
    constants: ModelEditorConstantAssignment[];
    invariants: string[];
    properties: string[];
    stateConstraint: string;
    actionConstraint: string;
    definitionOverrides: DefinitionOverride[];
    additionalDefinitions: string;
}

export interface ModelEditorPaths {
    specName: string;
    modelName: string;
    directory: string;
    tlaFilePath: string;
    cfgFilePath: string;
}

export interface DiscoveredSpecInfo {
    constants: string[];
    allOperators: string[];
    initCandidates: string[];
    nextCandidates: string[];
    temporalCandidates: string[];
    invariantCandidates: string[];
    propertyCandidates: string[];
}

export type TlcCheckingMode = 'bfs' | 'dfid' | 'simulate';

export interface TlcOptionsState {
    checkingMode: TlcCheckingMode;
    workers: number;
    dfidDepth: number;
    simulateTraces: number;
    simulateSeed: string;
    fpBits: number;
    enableProfiling: boolean;
    viewExpression: string;
    postCondition: string;
}

export const DEFAULT_TLC_OPTIONS: TlcOptionsState = {
    checkingMode: 'bfs',
    workers: 0,
    dfidDepth: 100,
    simulateTraces: 0,
    simulateSeed: '',
    fpBits: 1,
    enableProfiling: false,
    viewExpression: '',
    postCondition: ''
};

/** All TLC flags managed by the model editor. */
const MANAGED_TLC_FLAGS = new Set([
    '-workers', '-simulate', '-dfid', '-seed',
    '-fpbits', '-coverage', '-view', '-postcondition'
]);

export function tlcOptionsManagedFlags(): Set<string> {
    return MANAGED_TLC_FLAGS;
}

export function tlcOptionsToArgs(opts: TlcOptionsState): string[] {
    const args: string[] = [];
    if (opts.workers <= 0) {
        args.push('-workers', 'auto');
    } else {
        args.push('-workers', String(opts.workers));
    }
    if (opts.checkingMode === 'simulate') {
        args.push('-simulate');
        if (opts.simulateTraces > 0) {
            args.push(`num=${opts.simulateTraces}`);
        }
        if (opts.simulateSeed) {
            args.push('-seed', opts.simulateSeed);
        }
    } else if (opts.checkingMode === 'dfid') {
        args.push('-dfid', String(opts.dfidDepth));
    }
    if (opts.fpBits > 0) {
        args.push('-fpbits', String(opts.fpBits));
    }
    if (opts.enableProfiling) {
        args.push('-coverage', '1');
    }
    if (opts.viewExpression.trim()) {
        args.push('-view', opts.viewExpression.trim());
    }
    if (opts.postCondition.trim()) {
        args.push('-postCondition', opts.postCondition.trim());
    }
    return args;
}

const STATE_MARKER = '\\* MODEL_EDITOR_STATE ';

const CFG_DIRECTIVE_KEYWORDS = new Set([
    'INIT', 'NEXT', 'SPECIFICATION',
    'CONSTANT', 'CONSTANTS',
    'INVARIANT', 'INVARIANTS',
    'PROPERTY', 'PROPERTIES',
    'CHECK_DEADLOCK',
    'CONSTRAINT', 'ACTION_CONSTRAINT',
    'SYMMETRY', 'VIEW', 'ALIAS', 'POSTCONDITION',
    'TYPE_CONSTRAINT'
]);

const SUPPORTED_DIRECTIVES = new Set([
    'INIT', 'NEXT', 'SPECIFICATION',
    'CONSTANT', 'CONSTANTS',
    'INVARIANT', 'INVARIANTS',
    'PROPERTY', 'PROPERTIES',
    'CHECK_DEADLOCK',
    'CONSTRAINT', 'ACTION_CONSTRAINT'
]);

/**
 * Detects cfg directives that the model editor does not yet support.
 * Returns a deduplicated list of directive names found (e.g. ['SYMMETRY', 'CONSTRAINT']).
 */
export function detectUnsupportedDirectives(cfgContent: string): string[] {
    const found = new Set<string>();
    for (const line of cfgContent.split(/\r?\n/)) {
        const trimmed = line.trim();
        if (trimmed.length === 0 || trimmed.startsWith('\\*')) {
            continue;
        }
        const match = trimmed.match(/^([A-Z_]+)\b/);
        if (match && !SUPPORTED_DIRECTIVES.has(match[1])) {
            found.add(match[1]);
        }
    }
    return [...found].sort();
}

export function buildModelEditorPaths(specPath: string): ModelEditorPaths {
    const directory = path.dirname(specPath);
    const baseName = path.basename(specPath, path.extname(specPath));
    const specName = baseName;
    const modelName = `MC${specName}`;

    return {
        specName,
        modelName,
        directory,
        tlaFilePath: path.join(directory, `${modelName}.tla`),
        cfgFilePath: path.join(directory, `${modelName}.cfg`)
    };
}

export interface ModelEditorMarker {
    state: ModelEditorState;
    tlcOptions?: TlcOptionsState;
}

export function serializeModelEditorState(
    state: ModelEditorState,
    tlcOptions?: TlcOptionsState
): { tlaContent: string; cfgContent: string } {
    // Strip specPath from the stored marker — it's an absolute path
    // that becomes stale if the project moves. We reconstruct it
    // from the cfg file location on load.
    const { specPath: _stripped, ...stateWithoutPath } = state;
    const marker = { state: stateWithoutPath, tlcOptions };
    const meta = `${STATE_MARKER}${JSON.stringify(marker)}`;
    const tlaLines = [
        `---- MODULE ${state.modelName} ----`,
        `EXTENDS ${state.specName}, TLC`,
        '\\* Generated by the TLA+ Model Editor.',
        meta
    ];

    // Emit definition override operators in the TLA module
    for (const override of state.definitionOverrides ?? []) {
        if (override.name.trim() && override.expression.trim()) {
            const opName = overrideOperatorName(override.name);
            tlaLines.push(`${opName} == ${override.expression}`);
        }
    }

    // Emit additional definitions
    if (state.additionalDefinitions?.trim()) {
        tlaLines.push('');
        tlaLines.push(state.additionalDefinitions.trim());
    }

    tlaLines.push('====');

    const cfgLines = [
        '\\* Generated by the TLA+ Model Editor.',
        '\\* Manual edits may be overwritten by the editor.',
        meta
    ];

    if (state.behavior.kind === 'initNext') {
        if (state.behavior.init?.trim()) {
            cfgLines.push(`INIT ${state.behavior.init.trim()}`);
        }
        if (state.behavior.next?.trim()) {
            cfgLines.push(`NEXT ${state.behavior.next.trim()}`);
        }
    } else if (state.behavior.kind === 'temporal'
        && state.behavior.temporal?.trim()) {
        cfgLines.push(
            `SPECIFICATION ${state.behavior.temporal.trim()}`
        );
    }

    if (!state.checkDeadlock) {
        cfgLines.push('CHECK_DEADLOCK FALSE');
    }

    for (const assignment of state.constants) {
        const value = formatConstantValue(assignment);
        if (value.length > 0) {
            cfgLines.push(`CONSTANT ${assignment.name} = ${value}`);
        }
    }

    for (const invariant of state.invariants) {
        if (invariant.trim().length > 0) {
            cfgLines.push(`INVARIANT ${invariant.trim()}`);
        }
    }

    for (const property of state.properties) {
        if (property.trim().length > 0) {
            cfgLines.push(`PROPERTY ${property.trim()}`);
        }
    }

    if (state.stateConstraint?.trim()) {
        cfgLines.push(`CONSTRAINT ${state.stateConstraint.trim()}`);
    }

    if (state.actionConstraint?.trim()) {
        cfgLines.push(
            `ACTION_CONSTRAINT ${state.actionConstraint.trim()}`
        );
    }

    for (const override of state.definitionOverrides ?? []) {
        if (override.name.trim() && override.expression.trim()) {
            const opName = overrideOperatorName(override.name);
            cfgLines.push(
                `CONSTANT ${override.name} <- ${opName}`
            );
        }
    }

    return {
        tlaContent: tlaLines.join('\n'),
        cfgContent: cfgLines.join('\n')
    };
}

export interface ParsedModelEditor {
    state: ModelEditorState;
    tlcOptions?: TlcOptionsState;
}

export function parseModelEditorState(
    specPath: string,
    tlaContent: string,
    cfgContent: string
): ParsedModelEditor | undefined {
    const parsed = extractSerializedMarker(cfgContent)
        ?? extractSerializedMarker(tlaContent);
    if (parsed) {
        const state = parsed.state;
        // Backfill fields that may not exist in older state markers
        const s = state as unknown as Record<string, unknown>;
        if (!('specPath' in s) || !s.specPath) {
            state.specPath = specPath;
        }
        if (!('specName' in s) || !s.specName) {
            state.specName = path.basename(
                specPath, path.extname(specPath)
            );
        }
        if (!('stateConstraint' in s)) {
            state.stateConstraint = '';
        }
        if (!('actionConstraint' in s)) {
            state.actionConstraint = '';
        }
        if (!('definitionOverrides' in s)) {
            state.definitionOverrides = [];
        }
        if (!('additionalDefinitions' in s)) {
            state.additionalDefinitions = '';
        }
        return { state, tlcOptions: parsed.tlcOptions };
    }

    const paths = buildModelEditorPaths(specPath);
    const behavior: ModelEditorBehavior = { kind: 'none' };
    const initMatch = cfgContent.match(/^\s*INIT\s+(.+)$/m);
    const nextMatch = cfgContent.match(/^\s*NEXT\s+(.+)$/m);
    const temporalMatch = cfgContent.match(
        /^\s*SPECIFICATION\s+(.+)$/m
    );
    if (initMatch && nextMatch) {
        behavior.kind = 'initNext';
        behavior.init = initMatch[1].trim();
        behavior.next = nextMatch[1].trim();
    } else if (temporalMatch) {
        behavior.kind = 'temporal';
        behavior.temporal = temporalMatch[1].trim();
    }

    const constants = parseCfgConstants(cfgContent);

    const invariants = [
        ...cfgContent.matchAll(/^\s*INVARIANTS?\s+(.+)$/gm)
    ].flatMap((match) => splitSymbolList(match[1]));
    const properties = [
        ...cfgContent.matchAll(/^\s*PROPERT(?:Y|IES)\s+(.+)$/gm)
    ].flatMap((match) => splitSymbolList(match[1]));
    const checkDeadlock =
        !/^\s*CHECK_DEADLOCK\s+FALSE\s*$/m.test(cfgContent);

    const constraintMatch = cfgContent.match(
        /^\s*CONSTRAINT\s+(.+)$/m
    );
    const actionConstraintMatch = cfgContent.match(
        /^\s*ACTION_CONSTRAINT\s+(.+)$/m
    );

    const definitionOverrides = parseCfgOverrides(cfgContent);

    return {
        state: {
            specName: paths.specName,
            specPath,
            modelName: paths.modelName,
            behavior,
            checkDeadlock,
            constants,
            invariants,
            properties,
            stateConstraint: constraintMatch
                ? constraintMatch[1].trim() : '',
            actionConstraint: actionConstraintMatch
                ? actionConstraintMatch[1].trim() : '',
            definitionOverrides,
            additionalDefinitions: ''
        }
    };
}

export function discoverSpecInfo(specText: string): DiscoveredSpecInfo {
    const constants = new Set<string>();
    const operators = new Set<string>();

    for (const match of specText.matchAll(/^\s*CONSTANTS?\s+(.+)$/gm)) {
        const items = match[1]
            .split('\\*')[0]
            .trim();
        for (const item of splitTopLevelCommaSeparated(items)) {
            const cleaned = item.replace(/\s+$/g, '');
            if (cleaned.length > 0) {
                constants.add(cleaned);
            }
        }
    }

    for (const match of specText.matchAll(/^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==/gm)) {
        operators.add(match[1]);
    }

    const allOperators = [...operators].sort();
    const initNextPattern = /^(init|next)$/i;
    const nonInitNext = allOperators.filter(
        (op) => !initNextPattern.test(op)
    );
    return {
        constants: [...constants].sort(),
        allOperators,
        initCandidates: rankCandidates(allOperators, [/^Init$/i, /init/i]),
        nextCandidates: rankCandidates(allOperators, [/^Next$/i, /next/i]),
        temporalCandidates: rankCandidates(allOperators, [/^Spec$/i, /spec|behavior/i]),
        invariantCandidates: rankCandidates(nonInitNext, [/^TypeOK$/i, /inv|typeok|safety/i]),
        propertyCandidates: rankCandidates(nonInitNext, [/prop|live|liveness|fair/i]),
    };
}

/**
 * Extract the state marker from content.
 * Handles both old format (flat ModelEditorState) and new format
 * (wrapped { state, tlcOptions }).
 */
function extractSerializedMarker(
    content: string
): { state: ModelEditorState; tlcOptions?: TlcOptionsState } | undefined {
    const markerLine = content.split(/\r?\n/).find(
        (line) => line.startsWith(STATE_MARKER)
    );
    if (!markerLine) {
        return undefined;
    }

    try {
        const raw = JSON.parse(
            markerLine.substring(STATE_MARKER.length)
        );
        // New format: { state: {...}, tlcOptions: {...} }
        if (raw.state && typeof raw.state === 'object'
            && 'specName' in raw.state) {
            return {
                state: raw.state as ModelEditorState,
                tlcOptions: raw.tlcOptions as
                    TlcOptionsState | undefined
            };
        }
        // Old format: flat ModelEditorState
        if ('specName' in raw) {
            return { state: raw as ModelEditorState };
        }
        return undefined;
    } catch {
        return undefined;
    }
}

function parseCfgConstants(cfgContent: string): ModelEditorConstantAssignment[] {
    const constants: ModelEditorConstantAssignment[] = [];
    const lines = cfgContent.split(/\r?\n/);
    let inConstantsBlock = false;

    for (const line of lines) {
        const trimmed = line.trim();
        if (trimmed.length === 0) {
            continue;
        }
        if (trimmed.startsWith('\\*')) {
            continue;
        }

        if (/^CONSTANTS\b/.test(trimmed) && trimmed === 'CONSTANTS') {
            inConstantsBlock = true;
            continue;
        }

        if (trimmed.startsWith('CONSTANT ') || trimmed.startsWith('CONSTANTS ')) {
            const body = trimmed.replace(/^CONSTANTS?\s+/, '');
            // Skip definition overrides (name <- replacement)
            if (/^\S+\s+<-\s+\S+/.test(body)) {
                continue;
            }
            constants.push(...extractConstantAssignments(body));
            continue;
        }

        if (inConstantsBlock) {
            // A line starting with a directive keyword ends the block
            const kw = trimmed.match(/^([A-Z_]+)\b/);
            if (kw && CFG_DIRECTIVE_KEYWORDS.has(kw[1])) {
                inConstantsBlock = false;
                // Fall through so this line is handled below
            } else {
                const extracted = extractConstantAssignments(trimmed);
                if (extracted.length > 0) {
                    constants.push(...extracted);
                    continue;
                }
                inConstantsBlock = false;
            }
        }
    }

    return constants;
}

function extractConstantAssignments(text: string): ModelEditorConstantAssignment[] {
    const assignments: ModelEditorConstantAssignment[] = [];
    const assignmentRegex =
        /([A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?)\s*(?:=|<-)\s*(.+?)(?=(?:\s+[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s*(?:=|<-)\s*)|$)/g;

    for (let match = assignmentRegex.exec(text); match !== null; match = assignmentRegex.exec(text)) {
        const rawValue = match[2].trim();
        assignments.push({
            name: match[1],
            kind: inferConstantKind(rawValue),
            value: stripOuterBracesIfNeeded(rawValue)
        });
    }

    if (assignments.length === 0) {
        const symbol = text.trim();
        if (/^[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?$/.test(symbol)) {
            assignments.push({
                name: symbol,
                kind: 'modelValue',
                value: symbol
            });
        }
    }

    return assignments;
}

function formatConstantValue(assignment: ModelEditorConstantAssignment): string {
    const value = assignment.value.trim();
    if (value.length === 0) {
        return '';
    }

    if (assignment.kind === 'setModelValues') {
        return value.startsWith('{') ? value : `{${value}}`;
    }
    return value;
}

function inferConstantKind(value: string): ConstantAssignmentKind {
    const trimmed = value.trim();
    if (trimmed.startsWith('{') && trimmed.endsWith('}')) {
        return 'setModelValues';
    }
    if (/^[A-Za-z_][A-Za-z0-9_]*$/.test(trimmed)) {
        return 'modelValue';
    }
    return 'ordinary';
}

function stripOuterBracesIfNeeded(value: string): string {
    const trimmed = value.trim();
    if (trimmed.startsWith('{') && trimmed.endsWith('}')) {
        return trimmed.substring(1, trimmed.length - 1).trim();
    }
    return trimmed;
}

function rankCandidates(names: string[], priorities: RegExp[]): string[] {
    const prioritized = new Set<string>();
    for (const pattern of priorities) {
        for (const name of names) {
            if (pattern.test(name)) {
                prioritized.add(name);
            }
        }
    }
    for (const name of names) {
        prioritized.add(name);
    }
    return [...prioritized];
}

function splitTopLevelCommaSeparated(text: string): string[] {
    const items: string[] = [];
    let current = '';
    let depth = 0;

    for (const char of text) {
        if (char === ',' && depth === 0) {
            const trimmed = current.trim();
            if (trimmed.length > 0) {
                items.push(trimmed);
            }
            current = '';
            continue;
        }
        if (char === '(') {
            depth++;
        } else if (char === ')' && depth > 0) {
            depth--;
        }
        current += char;
    }

    const trimmed = current.trim();
    if (trimmed.length > 0) {
        items.push(trimmed);
    }
    return items;
}

function splitSymbolList(text: string): string[] {
    return text.trim().split(/\s+/).filter((item) => item.length > 0);
}

function overrideOperatorName(originalName: string): string {
    return `MC_${originalName.replace(/[^A-Za-z0-9_]/g, '_')}`;
}

function parseCfgOverrides(
    cfgContent: string
): DefinitionOverride[] {
    const overrides: DefinitionOverride[] = [];
    const regex = /^\s*CONSTANT\s+(\S+)\s+<-\s+(.+?)\s*$/gm;
    for (const match of cfgContent.matchAll(regex)) {
        overrides.push({
            name: match[1],
            expression: match[2]
        });
    }
    return overrides;
}
