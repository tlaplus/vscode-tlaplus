/**
 * tlcTraceToPuml.ts — Generate PlantUML directly from TLC trace output.
 *
 * Parses TLC dump output, discovers all interleavings of concurrent
 * processes, computes sequential vs. concurrent step regions, and
 * produces a PlantUML sequence diagram with `par`/`group` blocks.
 *
 * Ports the Python `compute_steps()` algorithm from tlc_sweep.py.
 */
import { TraceMessage } from '../webview/sequenceDiagram/types';
import { parseTlcTrace, parseAllTerminalTraces } from '../parsers/traceParser';

// ── Auto-color palette ───────────────────────────────────────

const CHANNEL_PALETTE = [
    { stroke: '#e53935', label: '#c62828' },   // red
    { stroke: '#1E88E5', label: '#1565C0' },   // blue
    { stroke: '#43A047', label: '#2E7D32' },   // green
    { stroke: '#FB8C00', label: '#E65100' },   // orange
    { stroke: '#8E24AA', label: '#6A1B9A' },   // purple
    { stroke: '#00ACC1', label: '#00838F' },   // teal
    { stroke: '#F4511E', label: '#BF360C' },   // deep-orange
    { stroke: '#3949AB', label: '#283593' },   // indigo
];

/** Palette for concurrent-chain group boxes. */
const GROUP_COLORS = [
    '#FF6B6B', '#00BBF9', '#6BCB77', '#FF9F1C', '#9B59B6', '#00F5D4',
];

// ── Public API ───────────────────────────────────────────────

/**
 * Convert raw TLC output directly to a PlantUML sequence diagram.
 *
 * If `dumpText` is provided (full TLC dump file), all terminal-state
 * interleavings are extracted and concurrent regions are rendered as
 * `par`/`group` blocks.  Otherwise, a single trace is parsed from
 * the TLC stdout/stderr.
 *
 * @param tlcOutput       Raw TLC stdout/stderr text.
 * @param options         Configuration options.
 * @returns               PlantUML text string, or null if no trace found.
 */
export function tlcTraceToPuml(
    tlcOutput: string,
    options: {
        traceVariable?: string;
        doneVariable?: string;
        title?: string;
        dumpText?: string;
    } = {},
): string | null {
    const traceVar = options.traceVariable ?? '_seqDiagramTrace';
    const doneVar = options.doneVariable ?? 'flow_complete';

    // ── Extract traces ───────────────────────────────────────
    let allTraces: TraceMessage[][];

    if (options.dumpText) {
        allTraces = parseAllTerminalTraces(options.dumpText, traceVar, doneVar);
    } else {
        const single = parseTlcTrace(tlcOutput, traceVar);
        allTraces = single && single.length > 0 ? [single] : [];
    }
    if (allTraces.length === 0) {
        // Fallback: parse single trace from TLC error output
        const fallback = parseTlcTrace(tlcOutput, traceVar);
        if (fallback && fallback.length > 0) {
            allTraces = [fallback];
        } else {
            return null;
        }
    }

    const canonical = allTraces[0];

    // ── Compute steps (sequential + concurrent) ──────────────
    const steps = computeSteps(allTraces);

    // ── Discover participants ────────────────────────────────
    const participantOrder: string[] = [];
    const seen = new Set<string>();
    for (const m of canonical) {
        for (const name of [m.src, m.dst]) {
            if (!seen.has(name)) {
                seen.add(name);
                participantOrder.push(name);
            }
        }
    }

    // ── Discover channels and assign colors ──────────────────
    // When messages have an explicit `ch` field, use that as the channel key.
    // Otherwise, fall back to the message type (`msg`) so every distinct
    // message type gets its own color automatically.
    const channelMap = new Map<string, { stroke: string; label: string }>();
    let colorIdx = 0;
    for (const m of canonical) {
        const key = m.ch ?? m.msg;
        if (key && !channelMap.has(key)) {
            channelMap.set(key, CHANNEL_PALETTE[colorIdx % CHANNEL_PALETTE.length]);
            colorIdx++;
        }
    }

    // ── Generate PlantUML ────────────────────────────────────
    const lines: string[] = [];

    lines.push('@startuml');
    lines.push('');

    // Skin settings
    lines.push('skinparam backgroundColor transparent');
    lines.push('skinparam sequenceMessageAlign center');
    lines.push('skinparam responseMessageBelowArrow true');
    lines.push('skinparam sequenceGroupBorderThickness 1');
    lines.push('skinparam sequenceBoxBorderColor #999999');
    lines.push('skinparam defaultFontName "Segoe UI", Arial, sans-serif');
    lines.push('skinparam defaultFontSize 12');
    lines.push('skinparam sequenceParticipantBorderColor #666666');
    lines.push('skinparam sequenceParticipantBackgroundColor #F5F5F5');
    lines.push('skinparam sequenceLifeLineBorderColor #BBBBBB');
    lines.push('skinparam sequenceDividerBorderColor #CCCCCC');
    lines.push('');

    lines.push('autonumber');
    lines.push('');

    if (options.title) {
        lines.push(`header ${esc(options.title)}`);
        lines.push('');
    }

    // Declare participants
    for (const p of participantOrder) {
        lines.push(`participant "${p}" as ${sanitize(p)}`);
    }
    lines.push('');

    // Render steps
    renderSteps(lines, steps, channelMap);

    lines.push('');
    lines.push('@enduml');

    return lines.join('\n');
}

// ── compute_steps — port from Python tlc_sweep.py ────────────

/** Hashable signature for a trace message. */
function msgSig(m: TraceMessage): string {
    return `${m.msg}|${m.src}|${m.dst}|${m.ch ?? ''}`;
}

/** A step is either sequential messages or a concurrent region. */
type Step = { type: 'sequential'; messages: TraceMessage[] }
           | { type: 'concurrent'; chains: TraceMessage[][] };

/**
 * Return the relative order of a subset of canonical indices within
 * each trace.  If all orderings are identical, the subset's internal
 * order is *stable* across traces.
 */
function orderOfSubset(
    traces: TraceMessage[][],
    sigIndices: string[],
    subset: Set<number>,
): number[][] {
    const orders: number[][] = [];
    for (const trace of traces) {
        // Build sig→position map for this trace
        const sigToPos = new Map<string, number>();
        for (let pos = 0; pos < trace.length; pos++) {
            sigToPos.set(msgSig(trace[pos]), pos);
        }
        // Sort subset indices by their position in this trace
        const ranked = [...subset].sort(
            (a, b) => (sigToPos.get(sigIndices[a]) ?? a) - (sigToPos.get(sigIndices[b]) ?? b)
        );
        orders.push(ranked);
    }
    return orders;
}

/** Check if all orderings in the list are identical. */
function allOrdersSame(orders: number[][]): boolean {
    if (orders.length <= 1) {return true;}
    const first = orders[0];
    for (let i = 1; i < orders.length; i++) {
        const o = orders[i];
        if (o.length !== first.length) {return false;}
        for (let j = 0; j < first.length; j++) {
            if (o[j] !== first[j]) {return false;}
        }
    }
    return true;
}

/**
 * Recursively split variant indices into causal chains.
 *
 * For each subset S (and complement S̄), if both have stable internal
 * order across all traces, they are independent concurrent chains.
 * Recurse into each half for further splits.
 */
function splitVariant(
    traces: TraceMessage[][],
    sigIndices: string[],
    indices: Set<number>,
): number[][] {
    if (indices.size <= 1) {
        return [[...indices]];
    }

    // Check if the whole set is already stable (single chain)
    const orders = orderOfSubset(traces, sigIndices, indices);
    if (allOrdersSame(orders)) {
        return [orders[0]];
    }

    const idxList = [...indices];
    const k = idxList.length;

    // Enumerate subsets of size 1…k//2 (complement covers other half)
    let bestSplit: {
        sSet: Set<number>;
        sBar: Set<number>;
        sOrder: number[];
        sbOrder: number[];
    } | null = null;

    outer:
    for (let size = 1; size <= Math.floor(k / 2); size++) {
        for (const combo of combinations(idxList, size)) {
            const sSet = new Set(combo);
            const sBar = new Set<number>();
            for (const idx of indices) {
                if (!sSet.has(idx)) {sBar.add(idx);}
            }
            if (sBar.size === 0) {continue;}

            // Avoid symmetric complements when size == k - size
            if (size === k - size && Math.min(...sSet) > Math.min(...sBar)) {
                continue;
            }

            const sOrders = orderOfSubset(traces, sigIndices, sSet);
            if (!allOrdersSame(sOrders)) {continue;}

            const sbOrders = orderOfSubset(traces, sigIndices, sBar);
            if (!allOrdersSame(sbOrders)) {continue;}

            bestSplit = {
                sSet, sBar,
                sOrder: sOrders[0],
                sbOrder: sbOrders[0],
            };
            break outer;
        }
    }

    if (!bestSplit) {
        // No valid 2-way split — each message is its own chain
        return [...indices].sort((a, b) => a - b).map(i => [i]);
    }

    // Recurse into each half
    const left = splitVariant(traces, sigIndices, bestSplit.sSet);
    const right = splitVariant(traces, sigIndices, bestSplit.sBar);
    return [...left, ...right];
}

/**
 * Derive sequential steps and concurrent regions from all trace variants.
 *
 * Algorithm:
 *   1. Segment the canonical trace into *fixed* positions (same message
 *      at that position in every trace) and *variant* ranges.
 *   2. Each fixed position becomes a sequential step.
 *   3. Each variant range is split into causal chains by finding subsets
 *      whose internal order is stable across all traces.
 */
function computeSteps(allTraces: TraceMessage[][]): Step[] {
    if (allTraces.length === 0) {return [];}

    const canonical = allTraces[0];
    const n = canonical.length;

    if (allTraces.length === 1) {
        // Single trace — all sequential
        return canonical.map(m => ({ type: 'sequential', messages: [m] }));
    }

    // Build sig→canonical index mapping
    const sigIndices = canonical.map(m => msgSig(m));

    // Phase 1: identify fixed vs. variant positions
    const fixed = new Array<boolean>(n).fill(true);
    for (let t = 1; t < allTraces.length; t++) {
        const trace = allTraces[t];
        for (let p = 0; p < n; p++) {
            if (fixed[p] && msgSig(trace[p]) !== sigIndices[p]) {
                fixed[p] = false;
            }
        }
    }

    // Phase 2: segment into fixed / variant ranges
    const steps: Step[] = [];
    let i = 0;
    while (i < n) {
        if (fixed[i]) {
            steps.push({ type: 'sequential', messages: [canonical[i]] });
            i++;
        } else {
            // Collect maximal contiguous variant range
            let j = i;
            while (j < n && !fixed[j]) {j++;}
            const variantIndices = new Set<number>();
            for (let x = i; x < j; x++) {variantIndices.add(x);}

            const chains = splitVariant(allTraces, sigIndices, variantIndices);
            // Convert index-chains to message-chains
            const msgChains = chains.map(chain => chain.map(idx => canonical[idx]));

            if (msgChains.length === 1) {
                // Single chain — emit as sequential steps
                for (const m of msgChains[0]) {
                    steps.push({ type: 'sequential', messages: [m] });
                }
            } else {
                steps.push({ type: 'concurrent', chains: msgChains });
            }
            i = j;
        }
    }
    return steps;
}

// ── Combinations generator ───────────────────────────────────

/** Generate all k-element combinations of `arr`. */
function* combinations<T>(arr: T[], k: number): Generator<T[]> {
    if (k === 0) { yield []; return; }
    if (k > arr.length) {return;}
    for (let i = 0; i <= arr.length - k; i++) {
        for (const rest of combinations(arr.slice(i + 1), k - 1)) {
            yield [arr[i], ...rest];
        }
    }
}

// ── PlantUML rendering ──────────────────────────────────────

function renderSteps(
    lines: string[],
    steps: Step[],
    channelMap: Map<string, { stroke: string; label: string }>,
): void {
    for (const step of steps) {
        if (step.type === 'sequential') {
            for (const m of step.messages) {
                renderMessage(lines, m, channelMap);
            }
        } else {
            renderConcurrentStep(lines, step.chains, channelMap);
        }
    }
}

function renderConcurrentStep(
    lines: string[],
    chains: TraceMessage[][],
    channelMap: Map<string, { stroke: string; label: string }>,
): void {
    if (chains.length === 0) {return;}
    if (chains.length === 1) {
        for (const m of chains[0]) {
            renderMessage(lines, m, channelMap);
        }
        return;
    }

    lines.push('');
    lines.push('par Concurrent Chains');
    for (let i = 0; i < chains.length; i++) {
        const color = GROUP_COLORS[i % GROUP_COLORS.length];
        lines.push(`  group #${color.replace('#', '')} Chain ${i + 1}`);
        for (const m of chains[i]) {
            lines.push(`    ${renderMessageStr(m, channelMap)}`);
        }
        lines.push('  end');
    }
    lines.push('end');
    lines.push('');
}

function renderMessage(
    lines: string[],
    m: TraceMessage,
    channelMap: Map<string, { stroke: string; label: string }>,
): void {
    lines.push(renderMessageStr(m, channelMap));
}

function renderMessageStr(
    m: TraceMessage,
    channelMap: Map<string, { stroke: string; label: string }>,
): string {
    const src = sanitize(m.src);
    const dst = sanitize(m.dst);
    // Use explicit ch if present, otherwise fall back to msg type for color lookup
    const key = m.ch ?? m.msg;
    const style = key ? channelMap.get(key) : undefined;

    // Arrow with color
    let arrowStr = '-';
    if (style) {
        arrowStr += `[#${style.stroke.replace('#', '')}]`;
    }
    arrowStr += '>';

    // Label with color + optional channel annotation
    let lbl: string;
    if (style && m.ch) {
        // Explicit channel: show channel name annotation below message
        const c = style.label.replace('#', '');
        lbl = `<color:#${c}><b>${esc(m.msg)}</b>\\n<size:9>${esc(m.ch)}</size></color>`;
    } else if (style) {
        // Auto-channel from msg type: colored but no annotation
        const c = style.label.replace('#', '');
        lbl = `<color:#${c}><b>${esc(m.msg)}</b></color>`;
    } else {
        lbl = `<b>${esc(m.msg)}</b>`;
    }

    return `${src} ${arrowStr} ${dst} : ${lbl}`;
}

// ── Helpers ──────────────────────────────────────────────────

function esc(s: string): string {
    return s.replace(/\\/g, '\\\\');
}

function sanitize(name: string): string {
    return name.replace(/[^a-zA-Z0-9_]/g, '_');
}
