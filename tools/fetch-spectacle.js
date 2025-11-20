#!/usr/bin/env node

/**
 * Fetch a pinned copy of Spectacle, prune it, and stage the assets under
 * resources/spectacle for the VS Code extension bundle.
 */

const fs = require('fs');
const path = require('path');
const os = require('os');
const { execSync } = require('child_process');
const crypto = require('crypto');

const DEFAULT_REPO = 'https://github.com/will62794/spectacle.git';
const PROJECT_ROOT = path.resolve(__dirname, '..');
const TARGET_DIR = path.join(PROJECT_ROOT, 'resources', 'spectacle');
const TMP_BASE = path.join(PROJECT_ROOT, 'tmp');
const FONT_VENDOR_DIR = path.join(PROJECT_ROOT, 'tools', 'vendor', 'spectacle-fonts');

function parseArgs() {
  const args = process.argv.slice(2);
  const parsed = { repo: DEFAULT_REPO };
  for (let i = 0; i < args.length; i += 1) {
    const token = args[i];
    if (token === '--ref' || token === '-r') {
      parsed.ref = args[++i];
    } else if (token === '--repo') {
      parsed.repo = args[++i];
    } else if (token === '--help' || token === '-h') {
      parsed.help = true;
    } else {
      throw new Error(`Unknown argument: ${token}`);
    }
  }
  return parsed;
}

function showHelp() {
  console.log(`Usage: node tools/fetch-spectacle.js --ref <commit-or-branch>

Options:
  --ref, -r   Git ref (commit SHA, tag, or branch) to checkout. Required.
  --repo      Alternate git remote URL (defaults to ${DEFAULT_REPO}).
  --help, -h  Show this message.
`);
}

function ensureRefProvided(ref) {
  if (!ref) {
    throw new Error('Missing required --ref <commit-or-branch> argument.');
  }
}

function run(cmd, options = {}) {
  execSync(cmd, { stdio: 'inherit', ...options });
}

function cloneRepository(repo, ref, checkoutDir) {
  console.log(`Cloning ${repo} into ${checkoutDir} ...`);
  run(`git clone ${repo} ${checkoutDir}`);
  console.log(`Fetching ref ${ref} ...`);
  run(`git fetch --depth 1 origin ${ref}`, { cwd: checkoutDir });
  console.log(`Checking out ${ref} ...`);
  run(`git checkout ${ref}`, { cwd: checkoutDir });
  const resolved = execSync('git rev-parse HEAD', { cwd: checkoutDir })
    .toString()
    .trim();
  console.log(`Checked out commit ${resolved}`);
  return resolved;
}

function resetTargetDir(target) {
  fs.rmSync(target, { recursive: true, force: true });
  fs.mkdirSync(target, { recursive: true });
}

function copyRelative(sourceRoot, entries, destinationRoot) {
  entries.forEach((entry) => {
    const src = path.join(sourceRoot, entry);
    const dest = path.join(destinationRoot, entry);
    if (!fs.existsSync(src)) {
      throw new Error(`Missing required Spectacle asset: ${entry}`);
    }
    fs.mkdirSync(path.dirname(dest), { recursive: true });
    const stats = fs.statSync(src);
    if (stats.isDirectory()) {
      fs.cpSync(src, dest, { recursive: true });
    } else {
      fs.copyFileSync(src, dest);
    }
  });
}

function buildManifest(destDir, metadata) {
  const files = [];
  const visit = (current) => {
    const entries = fs.readdirSync(current, { withFileTypes: true });
    entries.forEach((entry) => {
      const fullPath = path.join(current, entry.name);
      if (entry.isDirectory()) {
        visit(fullPath);
      } else {
        const relPath = path.relative(destDir, fullPath).replace(/\\/g, '/');
        const buffer = fs.readFileSync(fullPath);
        const hash = crypto.createHash('sha256').update(buffer).digest('hex');
        files.push({ path: relPath, bytes: buffer.length, sha256: hash });
      }
    });
  };
  visit(destDir);
  files.sort((a, b) => a.path.localeCompare(b.path));
  const manifest = {
    ...metadata,
    generatedAt: new Date().toISOString(),
    files,
  };
  const manifestPath = path.join(destDir, 'manifest.json');
  fs.writeFileSync(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
  console.log(`Wrote manifest with ${files.length} entries to ${manifestPath}`);
}

function formatBytes(bytes) {
  const units = ['B', 'KB', 'MB', 'GB'];
  let value = bytes;
  let unitIndex = 0;
  while (value >= 1024 && unitIndex < units.length - 1) {
    value /= 1024;
    unitIndex += 1;
  }
  return `${value.toFixed(2)} ${units[unitIndex]}`;
}

function directorySize(root) {
  let total = 0;
  const visit = (current) => {
    const entries = fs.readdirSync(current, { withFileTypes: true });
    entries.forEach((entry) => {
      const fullPath = path.join(current, entry.name);
      if (entry.isDirectory()) {
        visit(fullPath);
      } else {
        total += fs.statSync(fullPath).size;
      }
    });
  };
  visit(root);
  return total;
}

function main() {
  const args = parseArgs();
  if (args.help) {
    showHelp();
    process.exit(0);
  }
  ensureRefProvided(args.ref);

  fs.mkdirSync(TMP_BASE, { recursive: true });
  const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'spectacle-'));
  let resolvedCommit;
  try {
    resolvedCommit = cloneRepository(args.repo, args.ref, tempDir);
    resetTargetDir(TARGET_DIR);

    const DIR_WHITELIST = [
      'assets/css',
      'assets/favicon',
      'js/addon',
      'js/hash-sum',
      'js/lib',
    ];

    const FILE_WHITELIST = [
      'index.html',
      'style.css',
      'assets/glasses-svgrepo-com.svg',
      'assets/gear-spinner.svg',
      'assets/hide-icon.svg',
      'js/app.js',
      'js/eval.js',
      'js/main.js',
      'js/object_hash.js',
      'js/tlamode.js',
      'js/tree-sitter.js',
      'js/tree-sitter.wasm',
      'js/tree-sitter-tlaplus.wasm',
      'js/worker.js',
      'js/test_spec.js',
    ];

    copyRelative(tempDir, DIR_WHITELIST.concat(FILE_WHITELIST), TARGET_DIR);

    copyVendorFonts(TARGET_DIR);
    rewriteFontsCss(TARGET_DIR);
    pruneAssets(TARGET_DIR);
    rewriteIndexHtml(TARGET_DIR);
    rewriteStyleCss(TARGET_DIR);
    patchAppJs(TARGET_DIR);
    patchEvalJs(TARGET_DIR);

    buildManifest(TARGET_DIR, {
      sourceRepo: args.repo,
      requestedRef: args.ref,
      resolvedCommit,
    });

    const totalBytes = directorySize(TARGET_DIR);
    console.log(`Staged assets under ${TARGET_DIR} (${formatBytes(totalBytes)}).`);
  } finally {
    fs.rmSync(tempDir, { recursive: true, force: true });
  }
}

function copyVendorFonts(destDir) {
  if (!fs.existsSync(FONT_VENDOR_DIR)) {
    console.warn('Vendor fonts directory not found; skipping font copy.');
    return;
  }
  const dest = path.join(destDir, 'assets', 'fonts');
  fs.mkdirSync(dest, { recursive: true });
  fs.readdirSync(FONT_VENDOR_DIR).forEach((file) => {
    const src = path.join(FONT_VENDOR_DIR, file);
    if (fs.statSync(src).isFile()) {
      fs.copyFileSync(src, path.join(dest, file));
    }
  });
}

function rewriteFontsCss(destDir) {
  const cssPath = path.join(destDir, 'assets', 'css', 'fonts_JetBrainsMono_SourceCodePro.css');
  if (!fs.existsSync(cssPath)) {
    return;
  }
  const content = `@font-face {
  font-family: 'JetBrains Mono';
  font-style: normal;
  font-weight: 400;
  font-display: swap;
  src: url(../fonts/JetBrainsMono-Variable.ttf) format('truetype');
}
@font-face {
  font-family: 'Source Code Pro';
  font-style: normal;
  font-weight: 400;
  font-display: swap;
  src: url(../fonts/SourceCodePro-Variable.ttf) format('truetype');
}
`;
  fs.writeFileSync(cssPath, content);
}

function pruneAssets(destDir) {
  const bootstrapIconsDir = path.join(destDir, 'assets', 'css', 'bootstrap-icons-1.11.3');
  fs.rmSync(bootstrapIconsDir, { recursive: true, force: true });
}

function rewriteIndexHtml(destDir) {
  const indexPath = path.join(destDir, 'index.html');
  let html = fs.readFileSync(indexPath, 'utf8');
  html = html.replace(/\s*<link rel="stylesheet" href="assets\/css\/bootstrap-icons-1.11.3\/font\/bootstrap-icons.min.css">\n?/, '\n');
  html = html.replace(/\s*<link rel="preconnect" href="https:\/\/fonts\.googleapis\.com">\n?/, '\n');
  html = html.replace(/\s*<link rel="preconnect" href="https:\/\/fonts\.gstatic\.com" crossorigin>\n?/, '\n');
  html = html.replace(/\s*<script defer data-domain="will62794\.github\.io\/spectacle"[\s\S]*?window\.plausible[\s\S]*?<\/script>\n?/, '\n');
  html = html.replace(
    '<script>LANGUAGE_BASE_URL = "js";</script>',
    `    <script>
      (function () {
        let base = window.SPECTACLE_BASE_URL || '.';
        if (base.endsWith('/')) {
          base = base.slice(0, -1);
        }
        window.SPECTACLE_BASE_URL = base;
        const langBase = window.SPECTACLE_LANGUAGE_BASE_URL || base + '/js';
        window.SPECTACLE_LANGUAGE_BASE_URL = langBase;
        window.LANGUAGE_BASE_URL = langBase;
      })();
    </script>`
  );
  if (!html.includes('window.plausible')) {
    html = html.replace('</head>', '    <script>window.plausible = window.plausible || function () { /* noop analytics stub */ };</script>\n</head>');
  }
  if (!html.includes('__spectacleHistoryPatched')) {
    const historyPatch = `    <script>
      (function () {
        if (window.__spectacleHistoryPatched) {
          return;
        }
        window.__spectacleHistoryPatched = true;
        function wrapHistoryMethod(name) {
          if (!window.history || typeof window.history[name] !== 'function') {
            return;
          }
          const original = window.history[name];
          window.history[name] = function wrappedHistoryMethod() {
            try {
              return original.apply(this, arguments);
            } catch (error) {
              if (error && error.name === 'SecurityError') {
                console.warn('Spectacle history update blocked inside VS Code webview:', error);
                return null;
              }
              throw error;
            }
          };
        }
        wrapHistoryMethod('replaceState');
        wrapHistoryMethod('pushState');
      })();
    </script>`;
    html = html.replace('</head>', `${historyPatch}\n</head>`);
  }
  fs.writeFileSync(indexPath, html);
}

function rewriteStyleCss(destDir) {
  const stylePath = path.join(destDir, 'style.css');
  let style = fs.readFileSync(stylePath, 'utf8');
  style = style.replace(
    /background: url\([^)]*vsizegrip\.png[^)]*\) center center no-repeat #535353;/,
    'background: repeating-linear-gradient(45deg, #4f4f4f, #4f4f4f 4px, #6d6d6d 4px, #6d6d6d 8px);'
  );
  fs.writeFileSync(stylePath, style);
}

function patchAppJs(destDir) {
  const appPath = path.join(destDir, 'js', 'app.js');
  let code = fs.readFileSync(appPath, 'utf8');

  if (!code.includes('function resolveSpectaclePath')) {
    code = code.replace(
      'const LOCAL_SERVER_URL = "http://127.0.0.1:8000";',
      'const LOCAL_SERVER_URL = "http://127.0.0.1:8000";\nconst SPECTACLE_BASE_PATH = (typeof window !== "undefined" && window.SPECTACLE_BASE_URL ? window.SPECTACLE_BASE_URL : ".");\nconst NORMALIZED_SPECTACLE_BASE_PATH = SPECTACLE_BASE_PATH.endsWith("/") ? SPECTACLE_BASE_PATH.slice(0, -1) : SPECTACLE_BASE_PATH;\nfunction resolveSpectaclePath(relativePath) {\n    if (/^https?:/i.test(relativePath)) {\n        return relativePath;\n    }\n    let cleaned = relativePath;\n    while (cleaned.startsWith("/")) {\n        cleaned = cleaned.slice(1);\n    }\n    return `${NORMALIZED_SPECTACLE_BASE_PATH}/` + cleaned;\n}\n'
    );
  }

  if (!code.includes('const vscodeApi = typeof acquireVsCodeApi ===')) {
    const vscodeSnippet = 'const vscodeApi = typeof acquireVsCodeApi === "function" ? acquireVsCodeApi() : undefined;\nconst runningInsideVsCode = Boolean(vscodeApi);\nif (runningInsideVsCode) {\n    window.SPECTACLE_VSCODE_MODE = true;\n    window.addEventListener("message", (event) => {\n        const message = event.data;\n        if (!message || typeof message !== "object") {\n            return;\n        }\n        if (message.type === "spectacle:init" && typeof message.specText === "string") {\n            loadSpecText(message.specText, message.specUri || null);\n            if (vscodeApi) {\n                vscodeApi.postMessage({ type: "spectacle:initialized" });\n            }\n        }\n    });\n}\n';
    code = code.replace('let vizInstance = null;\n', `let vizInstance = null;\n\n${vscodeSnippet}\n`);
  }

  code = code.replace(/new Worker\("js\/worker\.js"\)/g, 'new Worker(resolveSpectaclePath("js/worker.js"))');

  code = code.replace(
    `            // Make a request to list files local files.\n            m.request(LOCAL_SERVER_URL + "/api/local_dir_files")\n                .then(data => {\n                    model.local_tla_file_list = data["tla_files"];\n                    console.log("Local files:", model.local_tla_file_list);\n                });`,
    `            // Make a request to list files local files.\n            if (window.SPECTACLE_ENABLE_LOCAL_SERVER) {\n                m.request(LOCAL_SERVER_URL + "/api/local_dir_files")\n                    .then(data => {\n                        model.local_tla_file_list = data["tla_files"];\n                        console.log("Local files:", model.local_tla_file_list);\n                    }).catch(err => console.warn("Local server unavailable", err));\n            }`
  );

  code = code.replace(
    '{class:"bi-exclamation-triangle", style:{"color":"red", "margin-left":"5px"}}, " Parse error.")',
    '{style:{"color":"red", "margin-left":"5px", "font-weight":"bold"}}, "⚠ Parse error.")'
  );

  code = code.replace('class: "bi bi-link fancy",', '');
  code = code.replace('class: "bi bi-gear",', '');
  code = code.replace('class: "bi bi-trash",', '');

  code = code.replace(
    'function loadSpecBox(hidden){\n    let loadFailedErrMsg = "Error fetching spec from given URL. Make sure the link is to a raw TLA+ file.";',
    'function loadSpecBox(hidden){\n    if (window.SPECTACLE_VSCODE_MODE) {\n        return null;\n    }\n    let loadFailedErrMsg = "Error fetching spec from given URL. Make sure the link is to a raw TLA+ file.";'
  );

  code = code.replace(
    '    loadSpecFromPath(model.specPath);\n}\n',
    '    if (!window.SPECTACLE_VSCODE_MODE) {\n        loadSpecFromPath(model.specPath);\n    }\n}\n'
  );

  if (!code.includes('spectacle:webview-ready')) {
    code = code.replace(
      "    document.addEventListener('keydown', handleKeyboardNavigation);",
      "    document.addEventListener('keydown', handleKeyboardNavigation);\n\n    if (vscodeApi) {\n        vscodeApi.postMessage({ type: 'spectacle:webview-ready' });\n    }"
    );
  }

  const routerOriginal = '    // m.mount(root, App)\n    m.route(root, "/home",\n        {\n            "/home": App,\n            "/eval_debug_graph": EvalDebugGraph,\n        });';
  const routerPatched = `    const disableSpectacleRouter = Boolean(typeof window !== "undefined" && window.SPECTACLE_ROUTER_DISABLE_HISTORY);
    if (disableSpectacleRouter) {
        let __spectacleRouteShimState = {};
        if (typeof m.route !== "function") {
            m.route = function () {};
        }
        if (typeof m.redraw !== "function") {
            m.redraw = function () {};
        }
        m.route.param = function (key) {
            if (typeof key === "string") {
                return __spectacleRouteShimState[key];
            }
            return __spectacleRouteShimState;
        };
        m.route.set = function (_path, params) {
            if (params && typeof params === "object") {
                __spectacleRouteShimState = params;
            } else {
                __spectacleRouteShimState = {};
            }
            if (typeof m.redraw === "function") {
                m.redraw();
            }
        };
        m.route.get = function () {
            return "/home";
        };
        m.mount(root, App);
    } else {
        m.route(root, "/home",
            {
                "/home": App,
                "/eval_debug_graph": EvalDebugGraph,
            });
    }`;
  if (code.includes(routerOriginal)) {
    code = code.replace(routerOriginal, routerPatched);
  }

  fs.writeFileSync(appPath, code);
}

function patchEvalJs(destDir) {
  const evalPath = path.join(destDir, 'js', 'eval.js');
  let code = fs.readFileSync(evalPath, 'utf8');
  if (code.includes('opName == "Assert"')) {
    return;
  }
  const marker = '    // FiniteSets ';
  const assertBlock = `    if (opName == "Assert") {\n        const conditionExpr = node.namedChildren[1];\n        const conditionVal = evalExpr(conditionExpr, ctx)[0]["val"];\n        assert(conditionVal instanceof BoolValue, "'Assert' expects a boolean expression.");\n        if (conditionVal.getVal()) {\n            return [ctx.withVal(conditionVal)];\n        }\n        let messageText = "";\n        if (node.namedChildren.length >= 3) {\n            const messageVal = evalExpr(node.namedChildren[2], ctx)[0]["val"];\n            if (messageVal instanceof StringValue) {\n                messageText = messageVal.getVal();\n            } else if (messageVal !== undefined && messageVal !== null) {\n                messageText = messageVal.toString();\n            }\n        }\n        const errorMessage = messageText ? \`TLC Assert failed: \${messageText}\` : "TLC Assert failed.";\n        throw new Error(errorMessage);\n    }\n\n${marker}`;
  if (!code.includes(marker)) {
    throw new Error('Failed to patch eval.js: marker not found');
  }
  code = code.replace(marker, assertBlock);
  fs.writeFileSync(evalPath, code);
}

if (require.main === module) {
  main();
}
