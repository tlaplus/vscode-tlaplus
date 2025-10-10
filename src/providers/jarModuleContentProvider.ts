import * as vscode from "vscode";
import * as path from "path";
import { readZipEntry } from "../utils/zipReader";

export const JAR_MODULE_SCHEME = "tlaplus-module";

export function createJarModuleUri(
  jarPath: string,
  entryPath: string,
): vscode.Uri {
  const query = new URLSearchParams({
    jar: jarPath,
    entry: entryPath,
  });
  return vscode.Uri.parse(
    `${JAR_MODULE_SCHEME}:///${entryPath}?${query.toString()}`,
  );
}

export class JarModuleContentProvider
  implements vscode.TextDocumentContentProvider
{
  async provideTextDocumentContent(uri: vscode.Uri): Promise<string> {
    const params = new URLSearchParams(uri.query);
    const jarPath = params.get("jar");
    const entryPath = params.get("entry");
    if (!jarPath || !entryPath) {
      throw new Error("Invalid module URI.");
    }

    const normalizedJarPath = jarPath.startsWith("file:")
      ? vscode.Uri.parse(jarPath).fsPath
      : jarPath;
    const entryContent = await readZipEntry(normalizedJarPath, entryPath);
    if (!entryContent) {
      throw new Error(
        `Unable to load module ${entryPath} from ${path.basename(jarPath)}`,
      );
    }

    return entryContent.toString("utf8");
  }
}
