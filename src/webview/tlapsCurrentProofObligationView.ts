import * as vscode from 'vscode';
import { TlapsProofObligationState } from '../model/tlaps';
import { URI } from 'vscode-uri';

export class TlapsProofObligationView implements vscode.WebviewViewProvider {
    public static readonly viewType = 'tlaplus.tlaps-current-proof-obligation';
    private view?: vscode.WebviewView;
    private oblState: TlapsProofObligationState | null = null;

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        _context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this.view = webviewView;
        this.show();
    }

    public showProofObligation(oblState: TlapsProofObligationState | null) {
        this.oblState = oblState;
        this.show();
    }

    private show() {
        if (this.view) {
            this.view.webview.html = this.makeHtml();
        }
    }

    private makeHtml() {
        const header =
            `<!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>Cat Coding</title>
            </head>
            <body>`;
        const footer =
            `</body>
            </html>`;
        let content = '<p>No obligation selected.</p>';
        if (this.oblState) {
            const loc = this.oblState.location;
            const uri = URI.parse(loc.uri);
            content = `<p>${uri.path.split(/\/|\\/).pop()}</p>`;
            if (loc.range.start.line === loc.range.end.line) {
                content += `<p>Line: ${loc.range.start.line}</p>`;
            } else {
                content += `<p>Lines: ${loc.range.start.line}-${loc.range.end.line}</p>`;
            }
            if (this.oblState.results) {
                content += '<ul>';
                this.oblState.results.forEach(r => {
                    const reason = r.reason ? ` <span style='opacity: 0.7'>(${r.reason})</span>` : '';
                    const meth = r.meth ? ` <span style='opacity: 0.7'>[${r.meth}]</span>` : '';
                    content += `<li>${r.prover}${meth}: ${r.status}${reason}</li>`;
                });
                content += '</ul>';
            } else {
                content += '<p>Not checked yet.</p>';
            }
            content += `<pre>${this.oblState.obligation}</pre>`;
        }
        return header + content + footer;
    }
}
