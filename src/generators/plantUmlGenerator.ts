/**
 * plantUmlGenerator.ts — Converts TraceData into PlantUML text.
 *
 * Requirements:
 *  1. All participants are declared (even those with no messages).
 *  2. Concurrent regions use `par` with nested `group` per chain.
 *  3. Channel colors come from channelStyles (consistent palette).
 *  4. Line/arrow style support (dashed, dotted).
 */
import {
    TraceData, TraceMessage, TraceStep, ChannelStyle,
    isConcurrentStep,
} from '../webview/sequenceDiagram/types';

// ── Defaults ─────────────────────────────────────────────────

const DEFAULT_STYLE: ChannelStyle = { stroke: '#616161', label: '#424242', name: '?' };

/** Palette for concurrent-chain group boxes. */
const GROUP_COLORS = [
    '#FF6B6B', '#00BBF9', '#6BCB77', '#FF9F1C', '#9B59B6', '#00F5D4',
];

// ── Helpers ──────────────────────────────────────────────────

function channelOf(msg: TraceMessage, data: TraceData): ChannelStyle {
    const styles = data.channelStyles ?? {};
    const ch = msg.ch;
    if (ch && styles[ch]) {return styles[ch];}
    return DEFAULT_STYLE;
}

/** Build the PlantUML arrow string including color and style. */
function arrow(msg: TraceMessage, data: TraceData): string {
    const style = channelOf(msg, data);
    const color = style.stroke;
    const lineStyle = msg.line;

    // PlantUML arrow syntax: -[#color]> or -[#color,dashed]>
    // For longer arrows use --> (dotted by default in PlantUML means longer)
    let arrowStr = '-';
    if (lineStyle === 'dashed') {
        arrowStr += `[#${color.replace('#', '')},dashed]`;
    } else if (lineStyle === 'dotted') {
        arrowStr += `[#${color.replace('#', '')},dotted]`;
    } else {
        arrowStr += `[#${color.replace('#', '')}]`;
    }
    arrowStr += '>';

    return arrowStr;
}

/** Escape PlantUML special characters in a label. */
function esc(s: string): string {
    // PlantUML uses \n for newline inside labels; escape backslashes
    return s.replace(/\\/g, '\\\\');
}

/** Build the colored label with channel name annotation. */
function label(msg: TraceMessage, data: TraceData): string {
    const style = channelOf(msg, data);
    const ch = msg.ch;
    const channelName = ch ? style.name : '';
    const color = style.label.replace('#', '');

    if (channelName && channelName !== '?') {
        return `<color:#${color}><b>${esc(msg.msg)}</b>\\n<size:9>${esc(channelName)}</size></color>`;
    }
    return `<color:#${color}><b>${esc(msg.msg)}</b></color>`;
}

// ── Main generator ───────────────────────────────────────────

/**
 * Convert TraceData to a PlantUML diagram string.
 */
export function traceDataToPlantUml(data: TraceData): string {
    const lines: string[] = [];

    lines.push('@startuml');
    lines.push('');

    // Skin settings for clean look
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

    // Auto-numbering
    lines.push('autonumber');
    lines.push('');

    // Parameter header
    const paramEntries = Object.entries(data.parameters);
    if (paramEntries.length > 0) {
        const headerText = paramEntries.map(([k, v]) => `${k}=${v}`).join('  ');
        lines.push(`header ${headerText}`);
        lines.push('');
    }

    // Declare ALL participants (even those with no messages)
    for (const p of data.participants) {
        lines.push(`participant "${p}" as ${sanitizeAlias(p)}`);
    }
    lines.push('');

    // Render steps
    if (data.steps) {
        renderSteps(lines, data.steps, data);
    } else {
        // Flat trace (no concurrent step regions) — render as sequential messages
        for (const msg of data.trace) {
            renderMessage(lines, msg, data);
        }
    }

    lines.push('');
    lines.push('@enduml');

    return lines.join('\n');
}

/** Render structured steps (sequential + concurrent). */
function renderSteps(lines: string[], steps: TraceStep[], data: TraceData): void {
    for (const step of steps) {
        if (isConcurrentStep(step)) {
            renderConcurrentStep(lines, step.concurrent, data);
        } else {
            // Sequential step: array of messages
            for (const msg of step) {
                renderMessage(lines, msg, data);
            }
        }
    }
}

/** Render a single message arrow. */
function renderMessage(lines: string[], msg: TraceMessage, data: TraceData): void {
    const src = sanitizeAlias(msg.src);
    const dst = sanitizeAlias(msg.dst);
    const arrowStr = arrow(msg, data);
    const lbl = label(msg, data);

    lines.push(`${src} ${arrowStr} ${dst} : ${lbl}`);
}

/**
 * Render a concurrent region using par with nested group blocks.
 *
 * PlantUML syntax:
 *   par Concurrent Chains
 *     group Chain 1
 *       A -> B : msg1
 *     end
 *     group Chain 2
 *       C -> D : msg2
 *     end
 *   end
 */
function renderConcurrentStep(
    lines: string[],
    chains: TraceMessage[][],
    data: TraceData,
): void {
    if (chains.length === 0) {return;}

    if (chains.length === 1) {
        // Single chain — no need for par/group wrapper
        for (const msg of chains[0]) {
            renderMessage(lines, msg, data);
        }
        return;
    }

    lines.push('');
    lines.push('par Concurrent Chains');

    for (let i = 0; i < chains.length; i++) {
        const chain = chains[i];
        const colorIdx = i % GROUP_COLORS.length;
        const color = GROUP_COLORS[colorIdx];

        // Use PlantUML group with color annotation
        lines.push(`  group #${color.replace('#', '')} Chain ${i + 1}`);

        for (const msg of chain) {
            const src = sanitizeAlias(msg.src);
            const dst = sanitizeAlias(msg.dst);
            lines.push(`    ${src} ${arrow(msg, data)} ${dst} : ${label(msg, data)}`);
        }

        lines.push('  end');
    }

    lines.push('end');
    lines.push('');
}

/**
 * Sanitize a participant name into a valid PlantUML alias.
 * PlantUML aliases must be alphanumeric (with underscores).
 */
function sanitizeAlias(name: string): string {
    return name.replace(/[^a-zA-Z0-9_]/g, '_');
}
