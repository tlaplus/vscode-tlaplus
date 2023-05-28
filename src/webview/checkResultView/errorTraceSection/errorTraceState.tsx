import { TreeItem } from '@microsoft/fast-components';
import * as React from 'react';
import { CollectionValue, ErrorTraceItem } from '../../../model/check';
import { CodeRangeLink } from '../common';
import { VSCodeTreeItem } from '../tree';
import { ErrorTraceSettings } from './errorTrace';
import { ErrorTraceVariable } from './errorTraceVariable';

interface ErrorTraceStateI {errorTraceItem: ErrorTraceItem, settings: ErrorTraceSettings, expanded: boolean}
export const ErrorTraceState = React.memo(({errorTraceItem, settings, expanded}: ErrorTraceStateI) => {

    const stateId = 'state-'+errorTraceItem.num;

    // Not using onExpandedChanged because collapseAll/expandAll would also trigger that event
    const handleExpand = (e: React.MouseEvent) => {
        if ((e.target as HTMLElement).id === stateId) {
            settings.setExpandValue(errorTraceItem.num-1, (e.currentTarget as TreeItem).expanded);
        }
    };
    const handleExpandKey = (e: React.KeyboardEvent<HTMLElement>) => {
        if ((e.target as HTMLElement).id === stateId && (e.key === 'ArrowLeft' || e.key === 'ArrowRight')) {
            settings.setExpandValue(errorTraceItem.num-1, (e.currentTarget as TreeItem).expanded);
        }
    };

    return (
        <VSCodeTreeItem id={stateId} expanded={expanded} onClick={handleExpand} onKeyDown={handleExpandKey}>
            <div className="error-trace-title">
                <span> {errorTraceItem.num}: {errorTraceItem.title} </span>
                <CodeRangeLink line=' >>' filepath={errorTraceItem.filePath} range={errorTraceItem.range}/>
            </div>

            {!expanded ? <VSCodeTreeItem/> :
                errorTraceItem.variables.items
                    .map(
                        (value) =>
                            <ErrorTraceVariable
                                key={value.id}
                                value={value as CollectionValue}
                                stateId={errorTraceItem.num}
                                settings={settings}/>)}
        </VSCodeTreeItem>
    );
});
