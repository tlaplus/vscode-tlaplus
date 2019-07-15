import * as vscode from 'vscode';
import * as path from 'path';
import {checkModel} from './cmd-check-model';
import {parseModule} from './cmd-parse-module';
import * as tasks from './tasks';
import {createParseModuleTask} from './task-parse-module';


let diagnostic: vscode.DiagnosticCollection;        // Holds all the error messages
const fileTasks = new Map<string, TLATasks>();      // Holds set of tasks linked to .tla file paths

/**
 * Set of taks, linked to a .tla file.
 */
class TLATasks {
    readonly parseModule: vscode.Task;
    readonly filePath: string;

    constructor(filePath: string, parseModule: vscode.Task) {
        this.parseModule = parseModule;
        this.filePath = filePath;
    }
}

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
    let cmdParse = vscode.commands.registerCommand('tlaplus.parse', () => parseModule(diagnostic));
    let cmdCheckModel = vscode.commands.registerCommand('tlaplus.model.check', () => checkModel(diagnostic));

    createFileTasks();

    let workspaceRoot = vscode.workspace.rootPath;
	if (!workspaceRoot) {
		return;
    }

    let pattern = path.join(workspaceRoot, '*.tla');
    let fileWatcher = vscode.workspace.createFileSystemWatcher(pattern);
    fileWatcher.onDidChange(e => {
        console.log('Did change ' + e);
        handleFileChange(e);
    });
	// fileWatcher.onDidCreate(() => tlaPromise = undefined);
	// fileWatcher.onDidDelete(() => tlaPromise = undefined);

    let taskProvider = vscode.tasks.registerTaskProvider('tla', {
        provideTasks: provideTasks,
        resolveTask(_task: vscode.Task): vscode.Task | undefined {
            return undefined;
		}
    });

    context.subscriptions.push(cmdParse);
    context.subscriptions.push(cmdCheckModel);
    context.subscriptions.push(taskProvider);
    context.subscriptions.push(fileWatcher);
}

export function deactivate() {}

async function handleFileChange(fileUri: vscode.Uri) {
    const filePath = fileUri.fsPath;
    const tasks = fileTasks.get(filePath);
    if (!tasks) {
        console.log('Tasks set not found for file `' + filePath + '`');
        vscode.window.showErrorMessage('File tasks not found.');
        return;
    }
    vscode.tasks.executeTask(tasks.parseModule);
}

function provideTasks(): vscode.Task[] {
    const tasks: vscode.Task[] = [];
    fileTasks.forEach((t, p) => tasks.push(t.parseModule));
    return tasks;
}

function createFileTasks() {
    const filePath = '/Users/andrew/Development/Workspaces/Personal/TLA/oms.tla';
    fileTasks.set(filePath, createTasksForTlaFile(filePath));
}

function createTasksForTlaFile(filePath: string): TLATasks {
    return new TLATasks(
        filePath,
        createParseModuleTask(filePath)
    );
}