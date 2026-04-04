import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import * as vscode from 'vscode';
import {
    SanyStdoutParser, hasTranslationChecksums, getDivergenceType
} from '../../../src/parsers/sany';

const FIXTURES_DIR = path.join(__dirname, '..', '..', '..', '..', 'tests', 'fixtures');

suite('PlusCal Divergence Detection Integration Tests', () => {
    let tempDir: string;

    setup(() => {
        tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-divergence-'));
    });

    teardown(() => {
        if (fs.existsSync(tempDir)) {
            fs.rmSync(tempDir, { recursive: true, force: true });
        }
    });

    test('SANY detects no divergence on clean file with matching checksums', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');
        const output = await runSanyOnFile(filePath);
        assert.ok(output.includes('Semantic processing of module DivergenceTest'),
            `SANY should parse successfully. Output: ${output.substring(0, 500)}`);

        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData), 'none');
    });

    test('SANY detects TLA+ translation divergence when translation is modified', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('/\\ TRUE', '/\\ FALSE');
        fs.writeFileSync(filePath, content, 'utf-8');

        const output = await runSanyOnFile(filePath);
        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData), 'tla');
    });

    test('SANY detects PlusCal divergence when algorithm is modified', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('  skip;', '  print "hello";');
        fs.writeFileSync(filePath, content, 'utf-8');

        const output = await runSanyOnFile(filePath);
        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData), 'pcal');
    });

    test('SANY detects both divergences when algorithm and translation are modified', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('  skip;', '  print "hello";');
        content = content.replace('/\\ TRUE', '/\\ FALSE');
        fs.writeFileSync(filePath, content, 'utf-8');

        const output = await runSanyOnFile(filePath);
        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData), 'both');
    });

    test('Pre-model-check: divergence detected on modified TLA+ translation', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('/\\ TRUE', '/\\ FALSE');
        fs.writeFileSync(filePath, content, 'utf-8');

        assert.strictEqual(hasTranslationChecksums(content), true,
            'File should have translation checksums');

        const { parseSpec } = await import('../../../src/commands/parseModule');
        const sanyData = await parseSpec(vscode.Uri.file(filePath));
        assert.strictEqual(getDivergenceType(sanyData), 'tla');
    });

    test('Pre-model-check: no divergence on clean file', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');
        const content = fs.readFileSync(filePath, 'utf-8');

        assert.strictEqual(hasTranslationChecksums(content), true,
            'File should have translation checksums');

        const { parseSpec } = await import('../../../src/commands/parseModule');
        const sanyData = await parseSpec(vscode.Uri.file(filePath));
        assert.strictEqual(getDivergenceType(sanyData), 'none');
    });

    test('Pre-model-check: skipped when no checksums', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        // Remove checksums from the BEGIN TRANSLATION line
        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace(
            /\\[*] BEGIN TRANSLATION \(.*\)/,
            '\\* BEGIN TRANSLATION'
        );
        fs.writeFileSync(filePath, content, 'utf-8');

        assert.strictEqual(hasTranslationChecksums(content), false,
            'File without checksum parenthetical should be skipped — no SANY needed');
    });

    function copyFixture(name: string): string {
        const src = path.join(FIXTURES_DIR, name);
        const dst = path.join(tempDir, name);
        fs.copyFileSync(src, dst);
        return dst;
    }

    async function runSanyOnFile(filePath: string): Promise<string> {
        const { runSany } = await import('../../../src/tla2tools');
        const procInfo = await runSany(filePath);

        let capturedOutput = '';
        procInfo.mergedOutput.on('data', (chunk) => {
            capturedOutput += chunk.toString();
        });

        await new Promise<void>((resolve, reject) => {
            if (procInfo.mergedOutput.readableEnded) {
                resolve();
                return;
            }
            const timer = setTimeout(
                () => reject(new Error('SANY did not finish in time')),
                10000
            );
            procInfo.mergedOutput.once('end', () => {
                clearTimeout(timer);
                resolve();
            });
        });

        return capturedOutput;
    }

    function parseSanyOutput(output: string): ReturnType<SanyStdoutParser['readAllSync']> {
        const parser = new SanyStdoutParser(output.split('\n'));
        return parser.readAllSync();
    }
});
