import * as React from 'react';
import { vscode } from './vscode';
import './coverageFileDeleted.css';

interface CoverageFileDeletedProps {
    fileName?: string;
}

export const CoverageFileDeleted: React.FC<CoverageFileDeletedProps> = ({ fileName }) => {
    const handleOpenFile = () => {
        vscode.executeCommand('tlaplus.coverage.visualize');
    };

    return (
        <div className="file-deleted-container">
            <div className="file-deleted-icon">
                <i className="codicon codicon-file"></i>
            </div>
            <h2>Coverage File Deleted</h2>
            <p className="file-deleted-message">
                {fileName
                    ? `The file "${fileName}" has been deleted.`
                    : 'The coverage file has been deleted.'}
            </p>
            <div className="file-deleted-instructions">
                <p>To visualize another coverage file:</p>
                <ul>
                    <li>Use Command Palette (<kbd>Ctrl+Shift+P</kbd> or <kbd>Cmd+Shift+P</kbd>)</li>
                    <li>Run "TLA+: Visualize simulation coverage"</li>
                </ul>
            </div>
            <div className="file-deleted-action">
                <button className="vscode-button" onClick={handleOpenFile}>
                    Open Another File
                </button>
            </div>
        </div>
    );
};