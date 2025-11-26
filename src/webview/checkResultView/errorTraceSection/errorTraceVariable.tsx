import * as React from 'react';
import { CollectionValue } from '../../../model/check';
import { vscode } from '../vscode';
import { ErrorTraceSettings } from './errorTrace';
import Ansi from '@cocalc/ansi-to-react';
import { VscodeTreeItem } from '@vscode-elements/react-elements';

interface ErrorTraceVariableI { value: CollectionValue, stateId: number, settings: ErrorTraceSettings }
export const ErrorTraceVariable = React.memo(({ value, stateId, settings }: ErrorTraceVariableI) => {

    if (stateId !== 1 && settings.hideModified && value.changeType === 'N') {
        return (null);
    }

    if (!checkFilter(value.key.toString(), settings.filter)) {
        return (null);
    }

    const copyButtonRef = React.useRef<HTMLElement>(null);
    const showButtonRef = React.useRef<HTMLElement>(null);

    React.useEffect(() => {
        const copyBtn = copyButtonRef.current;
        const showBtn = showButtonRef.current;

        const handleCopy = (event: MouseEvent) => {
            event.stopPropagation();
            event.stopImmediatePropagation();
            navigator.clipboard.writeText(value.str).then(
                () => vscode.showInfoMessage('Value has been copied to clipboard'),
                (err) => vscode.showErrorMessage('Failed to copy value: ' + err)
            );
        };

        const handleShow = (event: MouseEvent) => {
            event.stopPropagation();
            event.stopImmediatePropagation();
            vscode.showVariableValue(value.id);
        };

        copyBtn?.addEventListener('click', handleCopy);
        showBtn?.addEventListener('click', handleShow);

        return () => {
            copyBtn?.removeEventListener('click', handleCopy);
            showBtn?.removeEventListener('click', handleShow);
        };
    }, [value.id, value.str]);

    const changeHintKey = value.changeType as keyof typeof changeHints;
    const changeHint = changeHints[changeHintKey] ?? '';
    const changeTypeClass = 'value-' + value.changeType;
    const hasValueChildren = hasVariableChildrenToDisplay(value);
    const hasDeletedChildren = Array.isArray(value.deletedItems) && value.deletedItems.length > 0;
    const hasChildren = hasValueChildren || hasDeletedChildren;

    return (
        <VscodeTreeItem branch={hasChildren}>
            <div className="var-block">
                <div className="var-name" title={changeHint}>
                    <span className={changeTypeClass}> {value.key} </span>

                    {value.items &&
                        <span className="var-size" title="Size of the collection"> ({value.items.length}) </span>}

                    {value.changeType !== 'N' &&
                        <span className={`change-marker change-marker-${value.changeType}`}>
                            {value.changeType}
                        </span>}
                </div>

                <div className={'var-value ' + changeTypeClass} title={changeHint}>
                    <Ansi>{value.str}</Ansi>
                </div>

                <div className="var-menu">
                    <span
                        hidden={value.changeType !== 'D'}
                        title="Display value"
                        ref={showButtonRef}
                        className="var-button codicon codicon-link-external" />

                    <span
                        title="Copy value to clipboard"
                        ref={copyButtonRef}
                        className="var-button codicon codicon-copy" />
                </div>
            </div>


            {hasValueChildren &&
                (value as CollectionValue).items.map(
                    (childValue) =>
                        <ErrorTraceVariable
                            key={childValue.id}
                            value={childValue as CollectionValue}
                            stateId={stateId}
                            settings={settings} />)}

            {value.deletedItems &&
                value.deletedItems.map(
                    (childValue) =>
                        <ErrorTraceVariable
                            key={childValue.id}
                            value={childValue as CollectionValue}
                            stateId={stateId}
                            settings={settings} />)}
        </VscodeTreeItem>
    );
});

function hasVariableChildrenToDisplay(value: CollectionValue) {
    return value.items && (value.items.length > 1 || value.items.length === 1 && value.expandSingle);
}

const changeHints = {
    A: 'This item has been added since the previous state',
    M: 'This item has been modified since the previous state',
    D: 'This item has been deleted since the previous state',
    N: 'This item is unchanged since the previous state'
} as const;

function checkFilter(str: string, filterItems: string[]): boolean {
    if (filterItems.length === 0) {
        return true;
    }
    const eKey = str.toLowerCase();
    for (const filter of filterItems) {
        if (eKey.indexOf(filter) >= 0) {
            return true;
        }
    }
    return false;
}
