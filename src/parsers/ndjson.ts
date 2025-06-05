import { SimulationStats } from '../model/coverage';

export function parseNDJSON(content: string): SimulationStats[] {
    if (!content || content.trim().length === 0) {
        return [];
    }

    return content.trim().split('\n')
        .filter(line => line.trim().length > 0)
        .map(line => {
            try {
                const data = JSON.parse(line);
                return {
                    duration: data.duration || 0,
                    generated: data.generated || 0,
                    distinct: data.distinct || 0,
                    traces: data.traces || 0
                };
            } catch (e) {
                console.error('Failed to parse NDJSON line:', line, e);
                return null;
            }
        })
        .filter((item): item is SimulationStats => item !== null);
}