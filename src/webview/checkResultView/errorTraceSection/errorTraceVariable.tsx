import { TreeItem } from '@microsoft/fast-components';
import * as React from 'react';
import { CollectionValue } from '../../../model/check';
import { VSCodeTreeItem } from '../tree';
import { vscode } from '../vscode';
import { ErrorTraceSettings } from './errorTrace';
import { AnsiUp } from 'ansi_up';
const ansi_up = new AnsiUp();

interface ErrorTraceVariableI {value: CollectionValue, stateId: number, settings: ErrorTraceSettings}
export const ErrorTraceVariable = React.memo(({value, stateId, settings}: ErrorTraceVariableI) => {

    const [expanded, setExpanded] = React.useState(false);
    const handleExpanded = (e) => setExpanded((e.currentTarget as TreeItem).expanded);

    if (stateId !== 1 && settings.hideModified && value.changeType === 'N') {
        return (null);
    }

    if (!checkFilter(value.key.toString(), settings.filter)) {
        return (null);
    }

    const copyToClipboard = () => {
        navigator.clipboard.writeText(value.str);
        vscode.showInfoMessage('Value has been copied to clipboard');
    };

    const changeTypeClass = 'value-'+value.changeType;

    return (
        <VSCodeTreeItem expanded={expanded} onExpandedChanged={handleExpanded}>
            <div className="var-block">
                <div className="var-name" title={changeHints[value.changeType]}>
                    <span className={changeTypeClass}> {value.key} </span>

                    {value.items &&
                        <span className="var-size" title="Size of the collection"> ({value.items.length}) </span>}

                    {value.changeType !== 'N' &&
                        <span className={`change-marker change-marker-${value.changeType}`}>
                            {value.changeType}
                        </span>}
                </div>

                <div className={'var-value ' + changeTypeClass} title={changeHints[value.changeType]}>
                    {<div dangerouslySetInnerHTML={{ __html: ansi_up.ansi_to_html(value.str) }} />}
                </div>

                <div className="var-menu">
                    <span
                        hidden={value.changeType !== 'D'}
                        title="Dislpay value"
                        onClick={() => vscode.showVariableValue(value.id)}
                        className="var-button codicon codicon-link-external"/>

                    <span
                        title="Copy value to clipboard"
                        onClick={copyToClipboard}
                        className="var-button codicon codicon-copy"/>
                </div>
            </div>


            {hasVariableChildrenToDisplay(value) &&
                (!expanded ? <VSCodeTreeItem/> :
                    (value as CollectionValue).items.map(
                        (childValue) =>
                            <ErrorTraceVariable
                                key={childValue.id}
                                value={childValue as CollectionValue}
                                stateId={stateId}
                                settings={settings}/>))}

            {value.deletedItems &&
                (!expanded ? <VSCodeTreeItem/> :
                    value.deletedItems.map(
                        (childValue) =>
                            <ErrorTraceVariable
                                key={childValue.id}
                                value={childValue as CollectionValue}
                                stateId={stateId}
                                settings={settings}/>))}
        </VSCodeTreeItem>
    );
});

function hasVariableChildrenToDisplay(value: CollectionValue) {
    return value.items && (value.items.length > 1 || value.items.length === 1 && value.expandSingle);
}

const changeHints = {
    A: 'This item has been added since the previous state',
    M: 'This item has been modified since the previous state',
    D: 'This item has been deleted since the previous state'
};

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
