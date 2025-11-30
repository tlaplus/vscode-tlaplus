import * as fs from 'fs';
import * as path from 'path';
import { DCollection } from '../../diagnostic';

export async function copyLocalTlaModules(srcDir: string, dstDir: string): Promise<void> {
    await fs.promises.mkdir(dstDir, { recursive: true });
    const entries = await fs.promises.readdir(srcDir, { withFileTypes: true });
    await Promise.all(entries
        .filter((e) => e.isFile() && e.name.toLowerCase().endsWith('.tla'))
        .map(async (e) => {
            const src = path.join(srcDir, e.name);
            const dst = path.join(dstDir, e.name);
            await fs.promises.copyFile(src, dst);
        }));
}

export function remapDiagnostics(dCol: DCollection, fromDir: string, toDir: string) {
    const newCol = new DCollection();
    const fromPrefix = path.resolve(fromDir) + path.sep;
    const fromPrefixCmp = process.platform === 'win32' ? fromPrefix.toLowerCase() : fromPrefix;
    const toPrefix = path.resolve(toDir) + path.sep;

    const remapPath = (p: string) => {
        const abs = path.resolve(p);
        const absCmp = process.platform === 'win32' ? abs.toLowerCase() : abs;
        if (absCmp.startsWith(fromPrefixCmp)) {
            const rel = abs.substring(fromPrefix.length);
            return path.join(toPrefix, rel);
        }
        return p;
    };

    dCol.getMessages().forEach((msg) => {
        newCol.addMessage(
            remapPath(msg.filePath),
            msg.diagnostic.range,
            msg.diagnostic.message,
            msg.diagnostic.severity
        );
    });
    dCol.getModules().forEach((p) => newCol.addFilePath(remapPath(p)));
    return newCol;
}
