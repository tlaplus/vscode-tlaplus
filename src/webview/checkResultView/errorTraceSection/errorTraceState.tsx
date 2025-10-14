import * as React from 'react';
import { CollectionValue, ErrorTraceItem } from '../../../model/check';
import { CodeRangeLink } from '../common';
import { ErrorTraceVariable } from './errorTraceVariable';
import { VscodeTreeItem } from '@vscode-elements/react-elements';
import { ErrorTraceSettings } from './errorTrace';

type TreeItemElement = HTMLElementTagNameMap['vscode-tree-item'];

interface ErrorTraceStateI {
    errorTraceItem: ErrorTraceItem;
    settings: ErrorTraceSettings;
    registerTreeItem: (index: number, element: TreeItemElement | null) => void;
    stateIndex: number;
}

export const ErrorTraceState = React.memo(({
    errorTraceItem,
    settings,
    registerTreeItem,
    stateIndex
}: ErrorTraceStateI) => {

    const stateId = 'state-'+errorTraceItem.num;
    const treeItemElement = React.useRef<TreeItemElement | null>(null);

    const handleRef = React.useCallback((element: TreeItemElement | null) => {
        treeItemElement.current = element;
        registerTreeItem(stateIndex, element);
    }, [registerTreeItem, stateIndex]);

    React.useEffect(() => {
        const element = treeItemElement.current;
        if (!element) {
            return;
        }
        if (element.dataset.initialized !== 'true') {
            element.open = true;
            element.dataset.initialized = 'true';
        }
    }, []);

    return (
        <VscodeTreeItem id={stateId} ref={handleRef}>
            <div className="error-trace-title">
                <span> {errorTraceItem.num}: {errorTraceItem.title} </span>
                <CodeRangeLink line=' >>' filepath={errorTraceItem.filePath} range={errorTraceItem.range}/>
            </div>

            {errorTraceItem.variables.items
                .map(
                    (value) =>
                        <ErrorTraceVariable
                            key={value.id}
                            value={value as CollectionValue}
                            stateId={errorTraceItem.num}
                            settings={settings}/>)}
        </VscodeTreeItem>
    );
});
