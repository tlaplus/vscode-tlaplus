import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, checkModel } from './commands/checkModel';

export const CMD_MODEL_EDITOR_DISPLAY = 'tlaplus.model.editor.display';

// Cached HTML template for the WebView
let viewHtml: string | undefined;
let viewPanel: vscode.WebviewPanel | undefined;

/**
 * This is the extension side of the Model Editor web view. It currently supports only the most
 *  base of situations: behavior spec of type temporal and ordinary assignments for constant
 *  values. This was written as a quick proof of concept.
 * 
 * Observe comments notes below.
 */


export function showModelEditor(extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        createNewPanel();
        ensurePanelBody(extContext);
    } else {
        viewPanel.reveal();
    }
}

function createNewPanel() {
    const title = 'TLA+ Model Editor';
    viewPanel = vscode.window.createWebviewPanel(
        'modelEditor',
        title,
        vscode.ViewColumn.Beside,
        {
            enableScripts: true,
            localResourceRoots: [vscode.Uri.file(path.resolve(__dirname, '../../resources'))]
        }
    );
    viewPanel.iconPath = {
        dark: vscode.Uri.file(path.resolve(__dirname, '../../resources/images/preview-dark.svg')),
        light: vscode.Uri.file(path.resolve(__dirname, '../../resources/images/preview-light.svg')),
    };
    viewPanel.onDidDispose(() => {
        viewPanel = undefined;
    });
    viewPanel.webview.onDidReceiveMessage(message => {
        if (message.command === 'getOpenEditors') {
            if (viewPanel && viewPanel.visible) {
                // TODO for no clear reason "visible text editors" do not appear to include
                //          open text editors in tabs that do not have the focus in their
                //          pane.
                const textEditors = vscode.window.visibleTextEditors;
                const openEditorFilenames = new Array<string>();
                textEditors.forEach(function(editor) {
                    const filename = editor.document.fileName;

                    if (filename.toLowerCase().endsWith("tla")) {
                        openEditorFilenames.push(filename);
                    }
                });
                viewPanel.webview.postMessage({
                    editors: openEditorFilenames
                });
            }
        } else if (message.command === 'getModelConstants') {
            if (viewPanel && viewPanel.visible) {
                const editorFilename = message.filename;
                const textEditors = vscode.window.visibleTextEditors;
                let textEditor = null;
                for (let i = 0; i < textEditors.length; i++) {
                    if (textEditors[i].document.fileName == editorFilename) {
                        textEditor = textEditors[i];
                        break;
                    }
                }

                const constantsList = new Array<string>();
                if (textEditor) {
                    for (let i = 0; i < textEditor.document.lineCount; ++i) { 
                        const line = textEditor.document.lineAt(i);
                        const matches = /^[\s]*CONSTANT[S]?\s([a-zA-Z0-9\s\-,_]*)[\\\*]?.*$/g.exec(line.text);
                        if (matches) {
                            const names = matches[1].trim().split(',');
                            Array.prototype.push.apply(constantsList, names);
                        }
                    }
                }
                viewPanel.webview.postMessage({
                    modelConstants: constantsList
                });
            }
        } else if (message.command === 'stopModelCheck') {
            vscode.commands.executeCommand(CMD_CHECK_MODEL_STOP);
        } else if (message.command === 'startModelCheck') {
            const mcFilenames = mcFilenamesFromSpecFilename(message.filename);
            const mcTLAUri = vscode.Uri.file(mcFilenames[0]);
            vscode.commands.executeCommand(CMD_CHECK_MODEL_RUN, mcTLAUri);
        } else if (message.command === 'writeMCFiles') {
            const constants = message.constants;
            const spec = message.behaviorSpec;
            const filename = message.filename;
            const lastSeparatorIndex = filename.lastIndexOf(path.sep);
            const moduleName = filename.substring((lastSeparatorIndex + 1), (filename.length - 4));
            const mcFilenames = mcFilenamesFromSpecFilename(filename);

            if (writeMCFiles(mcFilenames[0], mcFilenames[1], moduleName, constants, spec)) {
                // TODO send ACK
            } else {
                // TOOO send NACK
            }
        } else if (message.command === 'showErrorMessage') {
            vscode.window.showErrorMessage(message.text);
        } else if (message.command === 'showInfoMessage') {
            vscode.window.showInformationMessage(message.text);
        }
    });
}

function ensurePanelBody(extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        return;
    }
    if (!viewHtml) {
        const resourcesDiskPath = vscode.Uri.file(
            path.join(extContext.extensionPath, 'resources')
        );
        const resourcesPath = viewPanel.webview.asWebviewUri(resourcesDiskPath);
        viewHtml = fs.readFileSync(path.join(extContext.extensionPath, 'resources', 'model-editor-view.html'), 'utf8');
        viewHtml = viewHtml
            .replace(/\${cspSource}/g, viewPanel.webview.cspSource)
            .replace(/\${resourcesPath}/g, String(resourcesPath));
    }
    viewPanel.webview.html = viewHtml;
}

function mcFilenamesFromSpecFilename(filename: string) {
    const lastSeparatorIndex = filename.lastIndexOf(path.sep);
    const parentDirectory = filename.substring(0, lastSeparatorIndex);
    const filenames = new Array<string>();
    
    filenames.push(parentDirectory + path.sep + "MC.tla");
    filenames.push(parentDirectory + path.sep + "MC.cfg");

    return filenames;
}

// TODO see file head comments concerning the only supported case at the moment
function writeMCFiles(mcTLAFile: string, mcCFGFile: string, moduleName: string, constants: Array<any>, spec: any) {
    let tlaConstantRun = "";
    let cfgConstantRun = "";
    let constantUniquer = 1;
    constants.forEach(function (constant) {
        const definition = "const_" + constantUniquer;
        tlaConstantRun += definition + " == " + constant.value + "\n";
        cfgConstantRun += "CONSTANT " + constant.name + " <- " + definition + "\n";
        constantUniquer++;
    });

    if (spec.kind == "temporal") {
        cfgConstantRun += "SPECIFICATION " + spec.temporal + "\n"; 
    } else if (spec.kind == "init-next") {
        cfgConstantRun += "INIT " + spec.init + "\n"; 
        cfgConstantRun += "NEXT " + spec.next + "\n"; 
    }


    const specification = "---- MODULE MC ----\nEXTENDS " + moduleName + ", TLC\n"
                            + tlaConstantRun
                            + "\n====================\n";
    fs.writeFile(mcTLAFile, specification, function (err) {
        if (err) {
            vscode.window.showErrorMessage("Problem encountered writing MC.tla: " + err);

            return false;
        }
    });

    fs.writeFile(mcCFGFile, cfgConstantRun, function (err) {
        if (err) {
            vscode.window.showErrorMessage("Problem encountered writing MC.cfg: " + err);

            // TODO delete MC.tla

            return false;
        }
    });

    return true;
}
