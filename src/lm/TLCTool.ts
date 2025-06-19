import * as vscode from 'vscode';
import * as path from 'path';
import { runTlc } from '../tla2tools';
import { getSpecFiles, mapTlcOutputLine, outChannel } from '../commands/checkModel';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';

export interface FileParameter {
	fileName: string;
}

export interface BehaviorLengthParameter {
	behaviorLength: number;
}

export interface FileWithBehaviorLengthParameter extends FileParameter, BehaviorLengthParameter {}

export class CheckModuleTool implements vscode.LanguageModelTool<FileParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        return runTLC(options, token, ['-modelcheck']);
    }
}
export class SmokeModuleTool implements vscode.LanguageModelTool<FileParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        // Terminate smoke testing, i.e., simulation after 3 seconds.
        return runTLC(options, token, ['-simulate'], ['-Dtlc2.TLC.stopAfter=3']);
    }
}
export class ExploreModuleTool implements vscode.LanguageModelTool<FileWithBehaviorLengthParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileWithBehaviorLengthParameter>,
        token: vscode.CancellationToken
    ) {
        // As a safeguard, terminate simulation after 3 seconds.
        return runTLC(options, token, ['-simulate', '-invlevel', options.input.behaviorLength.toString()], ['-Dtlc2.TLC.stopAfter=3']);
    }
}

async function runTLC(
    options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
    token: vscode.CancellationToken,
    extraOps: string[],
    extraJavaOpts: string[] = []
): Promise<vscode.LanguageModelToolResult> {
    // create an URI from the file name
    const input = options.input;
    const fileUri = vscode.Uri.file(input.fileName);
    // check if the file exists
    if (!fileUri) {
        return new vscode.LanguageModelToolResult(
            [new vscode.LanguageModelTextPart(`File ${input.fileName} does not exist`)]);
    }

    const specFiles = await getSpecFiles(fileUri, false);
    if (!specFiles) {
        // Extract the spec name from the file name.
        const specName = path.basename(input.fileName, path.extname(input.fileName));
        return new vscode.LanguageModelToolResult(
            [new vscode.LanguageModelTextPart(
                `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${input.fileName}. 
                Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC 
                guidelines.`)]
        );
    }

    // Run TLC with simulation mode
    const shareStats = vscode.workspace.getConfiguration().get<ShareOption>(CFG_TLC_STATISTICS_TYPE);
    if (shareStats !== ShareOption.DoNotShare) {
        extraJavaOpts.push('-Dtlc2.TLC.ide=TLAiVSCode');
    }
    const procInfo = await runTlc(
        specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath), false, extraOps, extraJavaOpts);
    if (procInfo === undefined) {
        return new vscode.LanguageModelToolResult([
            new vscode.LanguageModelTextPart('Failed to start TLC process')
        ]);
    }

    // Bind to output channel for display in VS Code output view.
    outChannel.bindTo(procInfo);

    // Create output collector
    const outputLines: string[] = [];

    // Return a promise that resolves when the process completes.
    return new Promise<vscode.LanguageModelToolResult>((resolve) => {
        // Custom handler for capturing output
        const stdoutHandler = (data: Buffer) => {
            const str = data.toString();
            const lines = str.split('\n');
            for (const line of lines) {
                if (line.trim() !== '') {
                    const cleanedLine = mapTlcOutputLine(line);
                    if (cleanedLine !== undefined) {
                        outputLines.push(cleanedLine);
                    }
                }
            }
        };

        // Add event listeners to capture stdout and stderr
        procInfo.process.stdout?.on('data', stdoutHandler);
        procInfo.process.stderr?.on('data', stdoutHandler);

        // Listen for process completion
        procInfo.process.on('close', (code) => {
            const result = new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(
                    `Model check completed with exit code ${code}.\n\n` +
					`Output:\n${outputLines.join('\n')}`
                )
            ]);
            resolve(result);
        });
    });
}