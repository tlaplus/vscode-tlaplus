import * as vscode from 'vscode';

/**
 * Value of Task.source that must be used in all TLA+ tasks.
 */
export const SOURCE = 'tla';

/**
 * Value of TaskDefinition.type that must be used in all TLA+ tasks.
 */
export const TYPE = 'tla';

/**
 * Interface of tasks on TLA+ modules.
 */
export interface TLATaskDefinition extends vscode.TaskDefinition {
    readonly filePath: string;
}
