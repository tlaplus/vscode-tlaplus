import * as vscode from 'vscode';
import * as tasks from './tasks';
import * as tools from './tla2tools';

/**
 * Task that parses .tla file in two phases:
 * 1. Transpile PlusCal code to TLA+ code.
 * 2. Check resulting TLA+ syntax.
 */
export function createParseModuleTask(filePath: string): vscode.Task {
    const opt: vscode.ProcessExecutionOptions = {};
    const taskDef = <tasks.TLATaskDefinition> {
        type: tasks.TYPE,
        filePath: filePath
    };
    const javaPath = tools.buildJavaPath();
    const execParts = [];
    execParts.push('"' + javaPath + '"');
    execParts.push('-cp');
    execParts.push(tools.toolsJarPath);
    execParts.push('pcal.trans');
    execParts.push('"' + filePath + '"');
    const exec = new vscode.ShellExecution(execParts.join(' '), opt);
    const task = new vscode.Task(taskDef, 'Parse module', tasks.SOURCE, exec);
    task.problemMatchers = ['$tsc-watch'];
    task.presentationOptions = {
        clear: true,
        echo: false,
        focus: false,
        panel: vscode.TaskPanelKind.Shared,
        reveal: vscode.TaskRevealKind.Never
    };
    return task;
}
