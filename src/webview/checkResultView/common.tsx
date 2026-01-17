import * as React from 'react';
import { Position, Range } from 'vscode';
import { vscode } from './vscode';
import { VscodeTableCell, VscodeTableHeaderCell } from '@vscode-elements/react-elements';

const baseLinkStyle: React.CSSProperties = {
    background: 'none',
    border: 'none',
    padding: 0,
    margin: 0,
    color: 'var(--vscode-textLink-foreground)',
    cursor: 'pointer',
    textDecoration: 'underline',
    font: 'inherit'
};

const tableCellClass = (alignRight: boolean) =>
    [alignRight ? 'text-align-right' : '', 'hidden-overflow-ellipsis', 'table-cell-padding']
        .filter(Boolean)
        .join(' ');

type ButtonProps = React.ButtonHTMLAttributes<HTMLButtonElement>;

export const VSCodeLink = React.forwardRef<HTMLButtonElement, ButtonProps>(
    ({children, style, className, ...rest}: ButtonProps, ref) => (
        <button
            ref={ref}
            type="button"
            className={className}
            style={{...baseLinkStyle, ...style}}
            {...rest}>
            {children}
        </button>
    )
);

export const EmptyLine = () => <div style={{marginTop: '1em'}}/>;

interface CodeRangeLinkI {line: string, filepath: string | undefined, range: Range}
export const CodeRangeLink = React.memo(({line, filepath, range}: CodeRangeLinkI) => (
    (!filepath || !range)
        ? <>{line}</>
        : <CodePositionLink line={line} filepath={filepath} position={range[0]}/>
));

interface CodePositionLinkI {line: string, filepath: string | undefined, position: Position | undefined}
export const CodePositionLink = React.memo(({line, filepath, position}: CodePositionLinkI) => {
    if (!filepath || !position) {
        return (<>{line}</>);
    }

    const location = {'line': position.line, 'character': position.character};
    const buttonRef = React.useRef<HTMLButtonElement>(null);

    React.useEffect(() => {
        const button = buttonRef.current;
        if (!button) {
            return;
        }

        const handleNativeClick = (event: MouseEvent) => {
            event.preventDefault();
            event.stopPropagation();

            const treeItem = button.closest('vscode-tree-item') as HTMLElement & {open?: boolean} | null;
            if (treeItem) {
                if (typeof treeItem.open === 'boolean') {
                    treeItem.open = true;
                } else {
                    treeItem.setAttribute('open', '');
                }
            }
            vscode.openFile(filepath, location);
        };

        button.addEventListener('click', handleNativeClick, true);
        return () => button.removeEventListener('click', handleNativeClick, true);
    }, [filepath, position.line, position.character]);

    return (
        <VSCodeLink ref={buttonRef}>
            {line}
        </VSCodeLink>
    );
});

interface DataGridCellI {
    value: React.JSX.Element | string | number,
    alignRight: boolean,
    tooltip?: string
}

export const DataGridCellHeader = React.memo(({value, alignRight, tooltip}: DataGridCellI) => (
    <VscodeTableHeaderCell
        title={tooltip}
        className={tableCellClass(alignRight)}>
        {value}
    </VscodeTableHeaderCell>
));

export const DataGridCellDefault = React.memo(({value, alignRight, tooltip}: DataGridCellI) => (
    <VscodeTableCell
        title={tooltip}
        className={tableCellClass(alignRight)}>
        {typeof value === 'number' ? num(value) : value}
    </VscodeTableCell>
));

const num = (n: number) => Number(n).toLocaleString().split(',').join(' ');
