import type * as React from 'react';


export const S: Record<string, React.CSSProperties> = {
    page: {
        fontFamily: 'var(--vscode-font-family)',
        color: 'var(--vscode-foreground)',
        padding: '12px',
        maxWidth: '980px',
        margin: '0 auto',
        boxSizing: 'border-box' as const
    },
    heading: { fontSize: '1.5rem', marginBottom: '0.5rem' },
    section: {
        border: '1px solid var(--vscode-panel-border)',
        borderRadius: '6px',
        padding: '12px',
        marginBottom: '16px'
    },
    label: { display: 'block', marginBottom: '8px' },
    input: {
        width: '100%',
        marginTop: '4px',
        padding: '6px 8px',
        color: 'var(--vscode-input-foreground)',
        background: 'var(--vscode-input-background)',
        border: '1px solid var(--vscode-input-border)',
        borderRadius: '4px',
        boxSizing: 'border-box'
    },
    compactInput: {
        minWidth: '180px',
        padding: '6px 8px',
        color: 'var(--vscode-input-foreground)',
        background: 'var(--vscode-dropdown-background)',
        border: '1px solid var(--vscode-dropdown-border)',
        borderRadius: '4px'
    },
    fileLink: {
        color: 'var(--vscode-textLink-foreground)',
        textDecoration: 'none',
        cursor: 'pointer'
    },
    modelNameRow: {
        display: 'flex',
        alignItems: 'center',
        flexWrap: 'wrap' as const,
        gap: '6px',
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)'
    },
    modelNameEdit: {
        display: 'flex',
        alignItems: 'center',
        flexWrap: 'wrap' as const,
        gap: '4px',
        marginTop: '2px'
    },
    chipButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-descriptionForeground)',
        cursor: 'pointer',
        fontSize: '0.9rem',
        padding: '2px 4px'
    },
    button: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer',
        whiteSpace: 'nowrap' as const
    },
    buttonPrimary: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer',
        fontWeight: 600,
        whiteSpace: 'nowrap' as const
    },
    buttonDisabled: {
        opacity: 0.5,
        cursor: 'default'
    },
    buttonGroup: {
        display: 'flex',
        gap: '8px',
        flexShrink: 0,
        flexWrap: 'wrap' as const
    },
    radioLabel: {
        display: 'flex',
        alignItems: 'center',
        gap: '8px',
        marginBottom: '6px',
        cursor: 'pointer'
    },
    initNextSummary: {
        display: 'flex',
        alignItems: 'center',
        gap: '10px',
        marginTop: '4px'
    },
    linkButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-textLink-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem',
        padding: '0',
        textDecoration: 'underline'
    },
    headerRow: {
        display: 'flex',
        justifyContent: 'space-between',
        gap: '12px',
        alignItems: 'flex-start',
        flexWrap: 'wrap' as const
    },
    smallText: {
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)'
    },
    errorText: {
        marginTop: '8px',
        fontSize: '0.9rem',
        color: 'var(--vscode-errorForeground)'
    },
    checkbox: {
        display: 'flex',
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    grid: {
        display: 'grid',
        gridTemplateColumns: 'repeat(auto-fit, minmax(240px, 1fr))',
        gap: '12px'
    },
    listField: { marginTop: '8px' },
    suggestionRow: {
        display: 'flex',
        flexWrap: 'wrap',
        gap: '6px',
        marginTop: '6px'
    },
    chip: {
        padding: '4px 8px',
        borderRadius: '12px',
        border: '1px solid var(--vscode-panel-border)',
        background: 'var(--vscode-editor-background)',
        color: 'var(--vscode-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem'
    },
    constantRow: {
        display: 'flex',
        flexWrap: 'wrap' as const,
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    constantName: { fontWeight: 600 },

    // Tab bar
    tabBar: {
        display: 'flex',
        flexWrap: 'wrap' as const,
        gap: '0',
        marginBottom: '16px'
    },
    tabWrap: {
        flex: '1 1 0',
        minWidth: '100px',
        display: 'flex',
        flexDirection: 'column' as const
    },
    tab: {
        padding: '8px 10px',
        background: 'transparent',
        color: 'var(--vscode-foreground)',
        border: 'none',
        cursor: 'pointer',
        fontSize: '0.9rem',
        opacity: 0.7,
        textAlign: 'center',
        outline: 'none',
        whiteSpace: 'nowrap' as const
    },
    tabActiveText: {
        opacity: 1,
        fontWeight: 600
    },
    tabIndicator: {
        height: '2px',
        background: 'var(--vscode-focusBorder)'
    },
    tabIndicatorHidden: {
        height: '2px',
        background: 'transparent'
    },

    // InfoTip (inline tooltip icon)
    infoTipWrap: {
        position: 'relative',
        display: 'inline-block',
        marginLeft: '6px',
        verticalAlign: 'middle',
        cursor: 'help'
    },
    infoTipIcon: {
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)',
        opacity: 0.7
    },
    infoTipPopover: {
        position: 'absolute',
        top: 'calc(100% + 6px)',
        left: '0',
        width: '280px',
        padding: '8px 12px',
        borderRadius: '4px',
        background: 'var(--vscode-editorHoverWidget-background)',
        border: '1px solid var(--vscode-editorHoverWidget-border)',
        color: 'var(--vscode-editorHoverWidget-foreground)',
        fontSize: '0.82rem',
        lineHeight: '1.45',
        textTransform: 'none' as const,
        letterSpacing: 'normal',
        fontWeight: 'normal' as const,
        zIndex: 100,
        pointerEvents: 'none',
        boxShadow: '0 2px 8px rgba(0,0,0,0.3)'
    },

    // Section heading (uppercase label with inline info)
    sectionHeading: {
        fontSize: '0.8rem',
        fontWeight: 600,
        letterSpacing: '0.5px',
        textTransform: 'uppercase' as const,
        color: 'var(--vscode-descriptionForeground)',
        marginBottom: '12px',
        display: 'flex',
        alignItems: 'center'
    },

    // Field label (inline with info tip)
    fieldLabel: {
        display: 'flex',
        alignItems: 'center',
        gap: '4px',
        marginBottom: '8px',
        flexWrap: 'wrap' as const
    },

    // Dirty field
    dirtyField: {
        position: 'relative',
        paddingLeft: '8px',
        marginBottom: '4px'
    },
    dirtyFieldHighlight: {
        borderLeft: '3px solid var(--vscode-editorWarning-foreground)',
        paddingLeft: '5px'
    },
    undoButton: {
        position: 'absolute',
        top: '0',
        right: '0',
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-descriptionForeground)',
        cursor: 'pointer',
        fontSize: '1rem',
        padding: '2px 6px'
    },

    // Spec options
    overrideRow: {
        display: 'flex',
        flexWrap: 'wrap' as const,
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    arrow: {
        color: 'var(--vscode-descriptionForeground)',
        fontSize: '1.1rem'
    },
    removeButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-errorForeground)',
        cursor: 'pointer',
        fontSize: '1rem',
        padding: '2px 6px'
    },
    addButton: {
        padding: '4px 10px',
        background: 'transparent',
        border: '1px dashed var(--vscode-panel-border)',
        borderRadius: '4px',
        color: 'var(--vscode-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem',
        marginTop: '4px'
    },

    // Custom suggestion dropdown (replaces native datalist)
    suggestBox: {
        position: 'absolute',
        top: '100%',
        left: '0',
        right: '0',
        maxHeight: '160px',
        overflowY: 'auto',
        background: 'var(--vscode-editorSuggestWidget-background)',
        border: '1px solid var(--vscode-editorSuggestWidget-border)',
        borderRadius: '4px',
        zIndex: 200,
        boxShadow: '0 2px 8px rgba(0,0,0,0.3)'
    },
    suggestItem: {
        padding: '4px 10px',
        cursor: 'pointer',
        fontSize: '0.9rem',
        color: 'var(--vscode-editorSuggestWidget-foreground)'
    }
};
