import * as vscode from 'vscode';
import * as path from 'path';
import { mapTlcOutputLine } from '../services/checkService';
import { CFG_TLC_STATISTICS_TYPE, ShareOption } from '../commands/tlcStatisticsCfg';
import { exists } from '../common';
import { CheckService } from '../services/checkService';
import { SpecFiles } from '../model/check';

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
    constructor(private readonly checkService: CheckService) {}

    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        const baseOpts = ['-modelcheck', '-cleanup'];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(this.checkService, options, token, [...baseOpts, ...extraOpts]);
    }
}
export class SmokeModuleTool implements vscode.LanguageModelTool<FileParameter> {
    constructor(private readonly checkService: CheckService) {}

    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        // Terminate smoke testing, i.e., simulation after 3 seconds.
        const baseOpts = ['-simulate', '-cleanup'];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(this.checkService, options, token, [...baseOpts, ...extraOpts], ['-Dtlc2.TLC.stopAfter=3']);
    }
}
export class ExploreModuleTool implements vscode.LanguageModelTool<FileWithBehaviorLengthParameter> {
    constructor(private readonly checkService: CheckService) {}

    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileWithBehaviorLengthParameter>,
        token: vscode.CancellationToken
    ) {
        // As a safeguard, terminate simulation after 3 seconds.
        const baseOpts = ['-simulate', '-cleanup', '-invlevel', options.input.behaviorLength.toString()];
        const extraOpts = options.input.extraOpts || [];
        return runTLC(
            this.checkService,
            options,
            token,
            [...baseOpts, ...extraOpts],
            ['-Dtlc2.TLC.stopAfter=3']
        );
    }
}

async function runTLC(
    checkService: CheckService,
    options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
    token: vscode.CancellationToken,
    extraOps: string[],
    extraJavaOpts: string[] = []
): Promise<vscode.LanguageModelToolResult> {
    const input = options.input;
    const cancellationResult = (filePath: string) => new vscode.LanguageModelToolResult([
        new vscode.LanguageModelTextPart(`Model checking cancelled for ${filePath}.`)
    ]);
    const maybeReturnOnCancel = (requestCancel?: () => void): vscode.LanguageModelToolResult | undefined => {
        if (token.isCancellationRequested) {
            requestCancel?.();
            return cancellationResult(input.fileName);
        }
        return undefined;
    };

    // create an URI from the file name
    const fileUri = vscode.Uri.file(input.fileName);

    const cancelBeforeStart = maybeReturnOnCancel();
    if (cancelBeforeStart) {
        return cancelBeforeStart;
    }

    // check if the file exists
    const inputFileExists = await exists(fileUri.fsPath);
    const cancelAfterExistenceCheck = maybeReturnOnCancel();
    if (cancelAfterExistenceCheck) {
        return cancelAfterExistenceCheck;
    }
    if (!inputFileExists) {
        return new vscode.LanguageModelToolResult(
            [new vscode.LanguageModelTextPart(`File ${input.fileName} does not exist`)]
        );
    }

    const specFiles = await checkService.resolveSpecFiles(fileUri, false, false);
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
    const sessionSpecFiles = input.configFileName
        ? new SpecFiles(specFiles.tlaFilePath, input.configFileName, specFiles.modelName, specFiles.outputDir)
        : specFiles;
    const session = await checkService.startSession(sessionSpecFiles, {
        showOptionsPrompt: false,
        showFullOutput: true,
        extraOpts: extraOps,
        extraJavaOpts,
    });
    const cancelAfterStart = maybeReturnOnCancel(() => session?.requestCancel());
    if (cancelAfterStart) {
        return cancelAfterStart;
    }
    if (session === undefined) {
        return new vscode.LanguageModelToolResult([
            new vscode.LanguageModelTextPart('Failed to start TLC process')
        ]);
    }

    const cancellationDisposable = token.onCancellationRequested(() => session.requestCancel());
    await session.completion;
    cancellationDisposable.dispose();
    if (token.isCancellationRequested || session.lifecycle === 'cancelled') {
        return cancellationResult(input.fileName);
    }

    const outputLines = session.rawOutput
        .split('\n')
        .map((line) => mapTlcOutputLine(line))
        .filter((line): line is string => line !== undefined && line.trim() !== '');
    return new vscode.LanguageModelToolResult([
        new vscode.LanguageModelTextPart(
            `Model check ${session.lifecycle} for ${input.fileName}.\n\nOutput:\n${outputLines.join('\n')}`
        )
    ]);
}
