import * as vscode from 'vscode';
import path = require('path');
import * as tools from './tla2tools';
import {TYPE as TASK_TYPE, SOURCE as TASK_SOURCE} from './tasks';

const tasks = new Map<string, vscode.Task>();

/**
 * Runs TLC on a TLA+ specification.
 */
export function checkModel(diagnostic: vscode.DiagnosticCollection) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return;
    }
    if (editor.document.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be checked as a model');
        return;
    }
    doCheckModel(editor.document.uri, diagnostic);
}

function doCheckModel(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    const task = getTask(fileUri.fsPath);
    if (!task) {
        return;
    }
    const exec = vscode.tasks.executeTask(task);
}

function getTask(filePath: string): vscode.Task | undefined {
    let task: vscode.Task | undefined = tasks.get(filePath);
    if (!task) {
        task = createTask(filePath);
        if (task) {
            tasks.set(filePath, task);
        }
    }
    return task;
}

/**
 * Creates task for running model checking process.
 */
function createTask(filePath: string): vscode.Task | undefined {
    let workDir = path.dirname(filePath);
    const javaPath = tools.buildJavaPath();
    if (!javaPath) {
        return undefined;
    }
    const opt: vscode.ProcessExecutionOptions = {
        cwd: workDir
    };
    const taskDef: vscode.TaskDefinition = {
        type: TASK_TYPE,
        filePath: filePath
    };
    const execParts = [];
    execParts.push('"' + javaPath + '"');
    execParts.push('-XX:+UseParallelGC');
    execParts.push('-jar');
    execParts.push(tools.toolsJarPath);
    execParts.push('"' + filePath + '"');
    const exec = new vscode.ShellExecution(execParts.join(' '), opt);
    const task = new vscode.Task(taskDef, 'Check model', TASK_SOURCE, exec);
    //task.problemMatchers = [{'$tla-pluscal-transpiler'}];
    task.presentationOptions = {
        clear: true,
        echo: false,
        focus: false,
        panel: vscode.TaskPanelKind.Shared,
        reveal: vscode.TaskRevealKind.Always
    };
    return task;
}
