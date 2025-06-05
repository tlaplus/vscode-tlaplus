export interface SimulationStats {
    duration: number;
    generated: number;
    distinct: number;
    traces: number;
}

export interface CoverageData {
    stats: SimulationStats[];
    fileName: string;
    lastUpdated: Date;
}