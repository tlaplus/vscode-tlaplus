import { TerminalProfile, ProviderResult, TerminalProfileProvider } from 'vscode';
import { runReplTerminal, getJavaPath, buildJavaOptions, toolsJarPath, TlaTool } from '../tla2tools';

export const CMD_RUN_REPL = 'tlaplus.repl.run';

export async function launchRepl(): Promise<void> {
    runReplTerminal();
}

export class REPLTerminalProfileProvider implements TerminalProfileProvider {
    provideTerminalProfile(): ProviderResult<TerminalProfile> {
        const javaPath = getJavaPath();
        const args = buildJavaOptions([], toolsJarPath);
        args.push(TlaTool.REPL);
        return {
            options: {
                name: 'TLA+ REPL',
                shellPath: javaPath,
                shellArgs: args
            }
        };
    }
}