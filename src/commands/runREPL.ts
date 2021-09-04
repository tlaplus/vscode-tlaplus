import { runReplTerminal } from '../tla2tools';

export const CMD_RUN_REPL = 'tlaplus.repl.run';

export async function launchRepl(): Promise<void> {
    runReplTerminal();
}