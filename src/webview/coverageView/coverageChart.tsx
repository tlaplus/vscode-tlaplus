import * as React from 'react';
import { useEffect, useRef, useMemo } from 'react';
import { CoverageData } from '../../model/coverage';
import { formatDuration } from '../common/formatters';
import {
    Chart as ChartJS,
    CategoryScale,
    LinearScale,
    PointElement,
    LineElement,
    Title,
    Tooltip,
    Legend,
    ChartOptions,
    ChartData
} from 'chart.js';
import { Line } from 'react-chartjs-2';
import './coverageChart.css';

// Register Chart.js components
ChartJS.register(
    CategoryScale,
    LinearScale,
    PointElement,
    LineElement,
    Title,
    Tooltip,
    Legend
);

interface CoverageChartProps {
    data: CoverageData;
}

export const CoverageChart: React.FC<CoverageChartProps> = ({ data }) => {
    const chartRef = useRef<ChartJS<'line'>>(null);

    // Prepare chart data
    const chartData: ChartData<'line'> = useMemo(() => ({
        labels: data.stats.map(stat => formatDuration(stat.duration, true)),
        datasets: [
            {
                label: 'Generated States',
                data: data.stats.map(stat => stat.generated),
                borderColor: 'rgb(59, 130, 246)', // Blue
                backgroundColor: 'rgba(59, 130, 246, 0.1)',
                tension: 0.1,
                pointRadius: 3,
                pointHoverRadius: 5,
            },
            {
                label: 'Distinct States',
                data: data.stats.map(stat => stat.distinct),
                borderColor: 'rgb(34, 197, 94)', // Green
                backgroundColor: 'rgba(34, 197, 94, 0.1)',
                tension: 0.1,
                pointRadius: 3,
                pointHoverRadius: 5,
            }
        ]
    }), [data.stats]);

    // Chart options
    const options: ChartOptions<'line'> = useMemo(() => ({
        responsive: true,
        maintainAspectRatio: false,
        plugins: {
            title: {
                display: true,
                text: 'States Over Time',
                font: {
                    size: 16,
                },
            },
            legend: {
                position: 'top' as const,
            },
            tooltip: {
                mode: 'index',
                intersect: false,
                callbacks: {
                    label: (context) => {
                        const label = context.dataset.label || '';
                        const value = context.parsed.y.toLocaleString();
                        return `${label}: ${value}`;
                    }
                }
            },
        },
        scales: {
            x: {
                display: true,
                title: {
                    display: true,
                    text: 'Duration',
                },
            },
            y: {
                display: true,
                title: {
                    display: true,
                    text: 'Number of States',
                },
                ticks: {
                    callback: function(value) {
                        return value.toLocaleString();
                    }
                },
            }
        },
        interaction: {
            mode: 'nearest',
            axis: 'x',
            intersect: false
        }
    }), []);

    // Update chart colors when theme changes
    useEffect(() => {
        const updateChartColors = () => {
            if (chartRef.current) {
                const chart = chartRef.current;
                const foreground = getComputedStyle(document.documentElement).getPropertyValue('--vscode-foreground');
                const border = getComputedStyle(document.documentElement).getPropertyValue('--vscode-panel-border');

                // Update title
                if (chart.options.plugins?.title) {
                    chart.options.plugins.title.color = foreground;
                }

                // Update legend
                if (chart.options.plugins?.legend?.labels) {
                    chart.options.plugins.legend.labels.color = foreground;
                }

                // Update scales
                if (chart.options.scales) {
                    ['x', 'y'].forEach(axis => {
                        const scale = chart.options.scales?.[axis];
                        if (scale) {
                            if (scale.title) {scale.title.color = foreground;}
                            if (scale.ticks) {scale.ticks.color = foreground;}
                            if (scale.grid) {scale.grid.color = border;}
                        }
                    });
                }

                chart.update();
            }
        };

        // Set initial colors
        updateChartColors();

        // Listen for theme changes
        const observer = new MutationObserver(updateChartColors);
        observer.observe(document.body, { attributes: true, attributeFilter: ['class'] });

        return () => observer.disconnect();
    }, []);

    return (
        <div className="coverage-chart-container">
            <div className="chart-wrapper">
                <Line ref={chartRef} data={chartData} options={options} />
            </div>
            <div className="chart-info">
                <p className="info-text">
                    <span className="codicon codicon-info"></span>
                    The chart shows how states are discovered over time during simulation.
                    A plateauing curve may indicate that the simulation has explored most reachable states.
                </p>
            </div>
        </div>
    );
};