import * as React from 'react';
import { createRoot } from 'react-dom/client';

const containerStyle: React.CSSProperties = {
    padding: '24px',
    fontFamily: 'var(--vscode-font-family)',
    color: 'var(--vscode-foreground)'
};

const headingStyle: React.CSSProperties = {
    fontSize: '1.25rem',
    margin: '0 0 8px 0'
};

const noteStyle: React.CSSProperties = {
    color: 'var(--vscode-descriptionForeground)',
    margin: 0
};

function ModelEditorApp(): JSX.Element {
    return (
        <React.StrictMode>
            <div style={containerStyle}>
                <h1 style={headingStyle}>TLA+ Model Editor</h1>
                <p style={noteStyle}>
                    The visual model editor is under construction.
                </p>
            </div>
        </React.StrictMode>
    );
}

const root = createRoot(document.getElementById('root') as HTMLElement);
root.render(<ModelEditorApp />);
