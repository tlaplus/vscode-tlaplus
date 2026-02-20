/**
 * traceParser.ts — Parse TLC output to extract trace messages.
 *
 * Ports the Python `parse_trace()` and `parse_all_terminal_traces()`
 * from tlc_sweep.py.
 */
import { TraceMessage } from '../webview/sequenceDiagram/types';

/**
 * Parse a trace variable from TLC output text.
 *
 * Looks for:  `/\ _seqDiagramTrace = << [msg |-> "X", src |-> "A", dst |-> "B", ch |-> "c"], … >>`
 *
 * @param output         Raw TLC stdout/stderr text.
 * @param traceVariable  Name of the trace variable (default: "_seqDiagramTrace").
 * @returns              Array of trace messages, or null if not found.
 */
export function parseTlcTrace(output: string, traceVariable = '_seqDiagramTrace'): TraceMessage[] | null {
    // Collapse whitespace — TLC wraps long lines, which can split delimiters.
    const flat = output.replace(/\s+/g, ' ');

    // Match:  /\ trace = << ... >>   (normal variable output)
    //   or:      trace = << ... >>   (ALIAS output — no /\ prefix)
    const escaped = traceVariable.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const pattern = new RegExp(`(?:/\\\\ )?${escaped} = <<(.*?)>>`, 'g');
    const matches: string[] = [];
    let m: RegExpExecArray | null;
    while ((m = pattern.exec(flat)) !== null) {
        matches.push(m[1]);
    }
    if (matches.length === 0) {return null;}

    // Use the LAST match (final state)
    const raw = matches[matches.length - 1].trim();
    if (!raw) {return [];}

    const entries: TraceMessage[] = [];
    const recPattern = /\[([^\]]+)\]/g;
    let rec: RegExpExecArray | null;
    while ((rec = recPattern.exec(raw)) !== null) {
        const body = rec[1];
        const dstMatch = body.match(/dst\s*\|->\s*"([^"]+)"/);
        const msgMatch = body.match(/msg\s*\|->\s*"([^"]+)"/);
        const srcMatch = body.match(/src\s*\|->\s*"([^"]+)"/);
        if (!dstMatch || !msgMatch || !srcMatch) {continue;}

        const entry: TraceMessage = {
            msg: msgMatch[1],
            src: srcMatch[1],
            dst: dstMatch[1],
        };
        const chMatch = body.match(/ch\s*\|->\s*"([^"]+)"/);
        if (chMatch) {
            entry.ch = chMatch[1];
        }
        entries.push(entry);
    }
    return entries;
}

/**
 * Extract ALL distinct terminal traces from a TLC dump file.
 *
 * Multiple terminal states arise when TLC explores different interleavings
 * of concurrent processes — each interleaving produces a different message
 * ordering in the trace variable.
 *
 * @param dumpText        Full text of a TLC dump file.
 * @param traceVariable   Name of the trace variable (default: "trace").
 * @param doneVariable    Name of the done-flag variable (default: "flow_complete").
 * @returns               Deduplicated list of traces.
 */
export function parseAllTerminalTraces(
    dumpText: string,
    traceVariable = '_seqDiagramTrace',
    doneVariable = 'flow_complete',
): TraceMessage[][] {
    const doneMarker = `${doneVariable} = TRUE`;
    const blocks = dumpText.split(/\r?\nState \d+:\r?\n/);
    const seen = new Set<string>();
    const traces: TraceMessage[][] = [];

    for (const block of blocks) {
        if (!block.includes(doneMarker)) {continue;}
        const trace = parseTlcTrace(block, traceVariable);
        if (!trace || trace.length === 0) {continue;}

        // Deduplicate by message signature sequence
        const sig = trace
            .map(m => `${m.msg}|${m.src}|${m.dst}|${m.ch ?? ''}`)
            .join(';;');
        if (!seen.has(sig)) {
            seen.add(sig);
            traces.push(trace);
        }
    }
    return traces;
}
