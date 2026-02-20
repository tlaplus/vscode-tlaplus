/**
 * Type definitions for PlusCal/TLA+ sequence diagram trace data.
 *
 * These types are used internally by the PlantUML generators.
 */

/** A single message in a trace (arrow between participants). */
export interface TraceMessage {
    /** Label text shown on the arrow. */
    msg: string;
    /** Source participant name. */
    src: string;
    /** Destination participant name. */
    dst: string;
    /** Channel identifier (key into channelStyles). */
    ch?: string;
    /** Arrow line style. Omit or leave undefined for solid (the default). */
    line?: 'dashed' | 'dotted';
}

/** Visual styling for a channel (arrow color + label color). */
export interface ChannelStyle {
    /** Stroke color for the arrow line, e.g. "#e53935". */
    stroke: string;
    /** Fill color for the label text, e.g. "#c62828". */
    label: string;
    /** Human-readable channel name, e.g. "RequestChannel". */
    name: string;
}

/**
 * A concurrent step: multiple chains that execute in parallel.
 * Each chain is an ordered array of messages.
 */
export interface ConcurrentStep {
    concurrent: TraceMessage[][];
}

/** A step is either a sequential message array or a concurrent region. */
export type TraceStep = TraceMessage[] | ConcurrentStep;

/** Top-level trace data structure (JSON root). */
export interface TraceData {
    /** Parameter key→value map describing this trace variant. */
    parameters: Record<string, string>;
    /** Ordered list of participant names (left-to-right). */
    participants: string[];
    /** Flat ordered list of all messages (legacy / flat view). */
    trace: TraceMessage[];
    /** Structured steps: sequential arrays or concurrent regions. */
    steps?: TraceStep[];
    /** Channel key → visual style mapping. */
    channelStyles?: Record<string, ChannelStyle>;
}

// ---------- Type guards ----------

export function isConcurrentStep(step: TraceStep): step is ConcurrentStep {
    return !Array.isArray(step) && 'concurrent' in step;
}
