/**
 * Formats a duration in seconds to a human-readable string
 * @param seconds The duration in seconds
 * @param compact Whether to use compact format (for charts) or full format
 * @returns Formatted duration string
 */
export function formatDuration(seconds: number, compact = false): string {
    const hours = Math.floor(seconds / 3600);
    const minutes = Math.floor((seconds % 3600) / 60);
    const secs = seconds % 60;

    if (compact) {
        if (hours > 0) {
            return `${hours}h${minutes > 0 ? ` ${minutes}m` : ''}`;
        } else if (minutes > 0) {
            return `${minutes}m`;
        } else {
            return `${secs}s`;
        }
    } else {
        if (hours > 0) {
            return `${hours}h ${minutes}m ${secs}s`;
        } else if (minutes > 0) {
            return `${minutes}m ${secs}s`;
        } else {
            return `${secs}s`;
        }
    }
}