import * as vscode from 'vscode';
import * as path from 'path';
import { runTlc, stopProcess, ToolProcessInfo } from '../tla2tools';
import { getSpecFiles, mapTlcOutputLine, outChannel } from '../commands/checkModel';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';
import { exists } from '../common';

export interface FileParameter {
	fileName: string;
	configFileName?: string;
	extraOpts?: string[];
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
        const baseOpts = ['-modelcheck', '-cleanup'];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(options, token, [...baseOpts, ...extraOpts]);
    }
}
export class SmokeModuleTool implements vscode.LanguageModelTool<FileParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        // Terminate smoke testing, i.e., simulation after 3 seconds.
        const baseOpts = ['-simulate', '-cleanup'];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(options, token, [...baseOpts, ...extraOpts], ['-Dtlc2.TLC.stopAfter=3']);
    }
}
export class ExploreModuleTool implements vscode.LanguageModelTool<FileWithBehaviorLengthParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileWithBehaviorLengthParameter>,
        token: vscode.CancellationToken
    ) {
        // As a safeguard, terminate simulation after 3 seconds.
        const baseOpts = ['-simulate', '-cleanup', '-invlevel', options.input.behaviorLength.toString()];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(
            options,
            token,
            [...baseOpts, ...extraOpts],
            ['-Dtlc2.TLC.stopAfter=3']
        );
    }
}

async function runTLC(
    options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
    token: vscode.CancellationToken,
    extraOps: string[],
    extraJavaOpts: string[] = []
): Promise<vscode.LanguageModelToolResult> {
    const cancellationResult = (filePath: string) => new vscode.LanguageModelToolResult([
        new vscode.LanguageModelTextPart(`Model checking cancelled for ${filePath}.`)
    ]);
    const maybeReturnOnCancel = (procInfo?: ToolProcessInfo): vscode.LanguageModelToolResult | undefined => {
        if (token.isCancellationRequested) {
            if (procInfo) {
                stopProcess(procInfo.process);
            }
            return cancellationResult(input.fileName);
        }
        return undefined;
    };

    // create an URI from the file name
    const input = options.input;
    const fileUri = vscode.Uri.file(input.fileName);
    // check if the file exists
    if (!fileUri) {
        return new vscode.LanguageModelToolResult(
            [new vscode.LanguageModelTextPart(`File ${input.fileName} does not exist`)]);
    }

    const cancelBeforeStart = maybeReturnOnCancel();
    if (cancelBeforeStart) {
        return cancelBeforeStart;
    }

    const specFiles = await getSpecFiles(fileUri, false, false);
    const cancelAfterSpecLookup = maybeReturnOnCancel();
    if (cancelAfterSpecLookup) {
        return cancelAfterSpecLookup;
    }
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

    // Check if the optional config parameter is provided.  If so, check if the config file exists.
    if (input.configFileName) {
        const configFileExists = await exists(vscode.Uri.file(input.configFileName).fsPath);
        const cancelAfterConfigCheck = maybeReturnOnCancel();
        if (cancelAfterConfigCheck) {
            return cancelAfterConfigCheck;
        }
        if (!configFileExists) {
            return new vscode.LanguageModelToolResult(
                [new vscode.LanguageModelTextPart(`Config file ${input.configFileName} does not exist`)]
            );
        }
    }

    // Run TLC with simulation mode
    const shareStats = vscode.workspace.getConfiguration().get<ShareOption>(CFG_TLC_STATISTICS_TYPE);
    if (shareStats !== ShareOption.DoNotShare) {
        extraJavaOpts.push('-Dtlc2.TLC.ide=TLAiVSCode');
    }
    const cfgFilePath = input.configFileName ? input.configFileName : specFiles.cfgFilePath;
    const procInfo = await runTlc(
        specFiles.tlaFilePath,
        cfgFilePath,
        false,
        extraOps,
        extraJavaOpts
    );
    const cancelAfterStart = maybeReturnOnCancel(procInfo);
    if (cancelAfterStart) {
        return cancelAfterStart;
    }
    if (procInfo === undefined) {
        return new vscode.LanguageModelToolResult([
            new vscode.LanguageModelTextPart('Failed to start TLC process')
        ]);
    }

    // Bind to output channel for display in VS Code output view.
    outChannel.bindTo(procInfo);

    // Create output collector
    const outputLines: string[] = [];
    let cancelled = false;
    const disposeCancellation = token.onCancellationRequested(() => {
        cancelled = true;
        stopProcess(procInfo.process);
    });
    const immediateCancellation = maybeReturnOnCancel(procInfo);
    if (immediateCancellation) {
        disposeCancellation.dispose();
        return immediateCancellation;
    }

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

        // Add event listener to capture merged output
        procInfo.mergedOutput.on('data', stdoutHandler);

        // Listen for process completion
        procInfo.process.on('close', (code) => {
            disposeCancellation.dispose();
            const result = new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(
                    cancelled
                        ? `Model checking cancelled for ${input.fileName}.`
                        : `Model check completed with exit code ${code}.\n\nOutput:\n${outputLines.join('\n')}`
                )
            ]);
            resolve(result);
        });
    });
}
