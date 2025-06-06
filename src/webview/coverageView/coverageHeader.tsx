import * as React from 'react';
import { VSCodeButton } from '@vscode/webview-ui-toolkit/react';
import { CoverageData } from '../../model/coverage';
import { vscode } from './vscode';
import { formatDuration } from '../common/formatters';
import './coverageHeader.css';

interface CoverageHeaderProps {
    data: CoverageData;
}

export const CoverageHeader: React.FC<CoverageHeaderProps> = ({ data }) => {
    const handleRefresh = () => {
        vscode.postMessage({ type: 'refresh' });
    };

    const lastStat = data.stats[data.stats.length - 1];

    return (
        <div className="coverage-header">
            <div className="header-content">
                <div className="header-info">
                    <h2>📊 Simulation Coverage: {data.fileName}</h2>
                    <div className="stats-summary">
                        {lastStat && (
                            <>
                                <span className="stat-item">
                                    <span className="stat-label">Duration:</span>
                                    <span className="stat-value">{formatDuration(lastStat.duration)}</span>
                                </span>
                                <span className="stat-item">
                                    <span className="stat-label">Generated:</span>
                                    <span className="stat-value">{lastStat.generated.toLocaleString()}</span>
                                </span>
                                <span className="stat-item">
                                    <span className="stat-label">Distinct:</span>
                                    <span className="stat-value">{lastStat.distinct.toLocaleString()}</span>
                                </span>
                                <span className="stat-item">
                                    <span className="stat-label">Traces:</span>
                                    <span className="stat-value">{lastStat.traces.toLocaleString()}</span>
                                </span>
                            </>
                        )}
                    </div>
                    <div className="last-updated">
                        Last updated: {new Date(data.lastUpdated).toLocaleTimeString()}
                    </div>
                </div>
                <div className="header-actions">
                    <VSCodeButton appearance="icon" onClick={handleRefresh}>
                        <span className="codicon codicon-refresh"></span>
                    </VSCodeButton>
                </div>
            </div>
        </div>
    );
};