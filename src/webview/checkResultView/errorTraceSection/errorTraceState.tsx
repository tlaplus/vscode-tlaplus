import * as React from 'react';
import { CollectionValue, ErrorTraceItem } from '../../../model/check';
import { CodeRangeLink } from '../common';
import { ErrorTraceVariable } from './errorTraceVariable';
import { VscodeTreeItem } from '@vscode-elements/react-elements';
import { ErrorTraceSettings } from './errorTrace';

type TreeItemElement = HTMLElementTagNameMap['vscode-tree-item'];

interface ErrorTraceStateI {errorTraceItem: ErrorTraceItem, settings: ErrorTraceSettings, expanded: boolean}
export const ErrorTraceState = React.memo(({errorTraceItem, settings, expanded}: ErrorTraceStateI) => {

    const stateId = 'state-'+errorTraceItem.num;

    // Not using onExpandedChanged because collapseAll/expandAll would also trigger that event
    const handleExpand = (event: React.MouseEvent<TreeItemElement>) => {
        settings.setExpandValue(errorTraceItem.num-1, event.currentTarget.open);
    };
    const handleExpandKey = (event: React.KeyboardEvent<TreeItemElement>) => {
        if (event.key === 'ArrowLeft' || event.key === 'ArrowRight') {
            settings.setExpandValue(errorTraceItem.num-1, event.currentTarget.open);
        }
    };

    return (
        <VscodeTreeItem id={stateId} open={expanded} onClick={handleExpand} onKeyDown={handleExpandKey}>
            <div className="error-trace-title">
                <span> {errorTraceItem.num}: {errorTraceItem.title} </span>
                <CodeRangeLink line=' >>' filepath={errorTraceItem.filePath} range={errorTraceItem.range}/>
            </div>

            {!expanded ? <VscodeTreeItem/> :
                errorTraceItem.variables.items
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
