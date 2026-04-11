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
        tempDir = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-divergence-')));
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
        assert.strictEqual(getDivergenceType(sanyData).size, 0);
    });

    test('SANY detects TLA+ translation divergence when translation is modified', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('/\\ TRUE', '/\\ FALSE');
        fs.writeFileSync(filePath, content, 'utf-8');

        const output = await runSanyOnFile(filePath);
        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData).get('DivergenceTest'), 'tla');
    });

    test('SANY detects PlusCal divergence when algorithm is modified', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');

        let content = fs.readFileSync(filePath, 'utf-8');
        content = content.replace('  skip;', '  print "hello";');
        fs.writeFileSync(filePath, content, 'utf-8');

        const output = await runSanyOnFile(filePath);
        const sanyData = parseSanyOutput(output);
        assert.strictEqual(getDivergenceType(sanyData).get('DivergenceTest'), 'pcal');
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
        assert.strictEqual(getDivergenceType(sanyData).get('DivergenceTest'), 'both');
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
        assert.strictEqual(getDivergenceType(sanyData).get('DivergenceTest'), 'tla');
    });

    test('Pre-model-check: no divergence on clean file', async function () {
        this.timeout(15000);
        const filePath = copyFixture('DivergenceTest.tla');
        const content = fs.readFileSync(filePath, 'utf-8');

        assert.strictEqual(hasTranslationChecksums(content), true,
            'File should have translation checksums');

        const { parseSpec } = await import('../../../src/commands/parseModule');
        const sanyData = await parseSpec(vscode.Uri.file(filePath));
        assert.strictEqual(getDivergenceType(sanyData).size, 0);
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

    test('SANY detects divergence in an imported module', async function () {
        this.timeout(15000);
        // Copy the fixture as an imported module and break its TLA+ translation.
        const helperPath = path.join(tempDir, 'DivHelper.tla');
        let helperContent = fs.readFileSync(path.join(FIXTURES_DIR, 'DivergenceTest.tla'), 'utf-8');
        helperContent = helperContent.replace('MODULE DivergenceTest', 'MODULE DivHelper');
        helperContent = helperContent.replace('/\\ TRUE', '/\\ FALSE');
        fs.writeFileSync(helperPath, helperContent, 'utf-8');

        // Create a clean root module that extends DivHelper.
        const rootPath = path.join(tempDir, 'CleanRoot.tla');
        fs.writeFileSync(rootPath,
            '---- MODULE CleanRoot ----\nEXTENDS DivHelper\n\nCleanOp == TRUE\n\n====\n', 'utf-8');

        const output = await runSanyOnFile(rootPath);
        const sanyData = parseSanyOutput(output);
        const divergence = getDivergenceType(sanyData);

        assert.ok(divergence.size > 0, 'SANY should report divergence from the imported module');
        assert.ok(divergence.has('DivHelper'),
            `Divergence should be attributed to DivHelper, got: ${[...divergence.keys()]}`);
        assert.strictEqual(divergence.has('CleanRoot'), false,
            'Clean root should not appear in divergence map');
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
