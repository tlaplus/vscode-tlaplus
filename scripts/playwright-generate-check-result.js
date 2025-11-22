#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const { PassThrough } = require('stream');
const Module = require('module');

const repoRoot = path.resolve(__dirname, '..');
const outDir = path.join(repoRoot, 'out', 'src');
const fixturesDir = path.join(repoRoot, 'tests', 'fixtures', 'playwright');
const outputPath = path.join(fixturesDir, 'check-result.json');
const sourcePath = path.join(repoRoot, 'tests', 'fixtures', 'parsers', 'tlc', 'error-trace.out');

if (!fs.existsSync(path.join(outDir, 'parsers', 'tlc.js'))) {
  console.error('Compiled output not found. Run `npm run compile` first.');
  process.exit(1);
}

const originalLoad = Module._load;
Module._load = function(request, parent, isMain) {
  if (request === 'vscode') {
    class Position {
      constructor(line, character) {
        this.line = line;
        this.character = character;
      }
    }
    class Range {
      constructor(start, end) {
        this.start = start;
        this.end = end;
      }
    }
    return {
      Range,
      Position,
      DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2 },
      window: {
        showErrorMessage: () => {},
        showWarningMessage: () => {}
      }
    };
  }
  return originalLoad(request, parent, isMain);
};

const parserMod = require(path.join(outDir, 'parsers', 'tlc.js'));
const modelMod = require(path.join(outDir, 'model', 'check.js'));

const buffer = fs.readFileSync(sourcePath);
const stream = new PassThrough();
stream.end(buffer);
let lastResult = null;
const parser = new parserMod.TlcModelCheckerStdoutParser(
  modelMod.ModelCheckResultSource.OutFile,
  stream,
  undefined,
  false,
  (result) => {
    lastResult = result;
  }
);

parser.readAll().then(() => {
  if (!lastResult) {
    throw new Error('Failed to parse TLC output');
  }
  lastResult.errors?.forEach(error => error.errorTrace?.forEach(state => {
    state.filePath = 'Spec.tla';
    state.range = [{ line: 0, character: 0 }, { line: 0, character: 0 }];
  }));
  fs.mkdirSync(fixturesDir, { recursive: true });
  fs.writeFileSync(outputPath, JSON.stringify(lastResult, null, 2));
  console.log(`Wrote ${outputPath}`);
}).catch(err => {
  console.error(err);
  process.exit(1);
});
