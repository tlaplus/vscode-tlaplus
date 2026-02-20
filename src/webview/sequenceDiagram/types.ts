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
    /** Channel identifier used for color grouping. */
    ch?: string;
    /** Arrow line style. Omit or leave undefined for solid (the default). */
    line?: 'dashed' | 'dotted';
}
