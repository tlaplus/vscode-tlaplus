import * as assert from 'assert';
import * as path from 'path';
import { buildJavaOptions, buildTlcOptions, buildPlusCalOptions, splitArguments, extractFingerprintFromTrace } from '../../src/tla2tools';

suite('TLA+ Tools Test Suite', () => {

    test('Builds PlusCal options with no custom settings', async () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', []),
            ['-nocfg', 'module.tla']
        );
    });

    test('Puts PlusCal custom options before module name', async () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', ['-lineWidth', '100']),
            ['-lineWidth', '100', '-nocfg', 'module.tla']
        );
    });

    test('Provides default TLC options', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', []);
        assert.strictEqual(result[0], 'module.tla');
        assert.strictEqual(result[1], '-tool');
        assert.strictEqual(result[2], '-modelcheck');
        assert.strictEqual(result[3], '-config');
        assert.strictEqual(result[4], '/path/to/module.cfg');
        // -fp and -dumptrace are automatically added in BFS mode
        assert.ok(result.includes('-fp'));
        assert.ok(result.includes('-dumptrace'));
    });

    test('Adds custom TLC options', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-deadlock', '-checkpoint', '5']);
        assert.strictEqual(result[0], 'module.tla');
        assert.strictEqual(result[1], '-tool');
        assert.strictEqual(result[2], '-modelcheck');
        assert.strictEqual(result[3], '-config');
        assert.strictEqual(result[4], '/path/to/module.cfg');
        // Custom options should be present
        assert.ok(result.includes('-deadlock'));
        assert.ok(result.includes('-checkpoint'));
        const checkpointIdx = result.indexOf('-checkpoint');
        assert.strictEqual(result[checkpointIdx + 1], '5');
    });

    test('Allows to change module .cfg in TLC options', async () => {
        const result = await buildTlcOptions(
            '/path/to/module.tla',
            '/path/to/module.cfg',
            ['-deadlock', '-config', '/path/to/another.cfg', '-nowarning']
        );
        assert.strictEqual(result[0], 'module.tla');
        assert.strictEqual(result[1], '-tool');
        assert.strictEqual(result[2], '-modelcheck');
        assert.strictEqual(result[3], '-config');
        assert.strictEqual(result[4], '/path/to/another.cfg');
        assert.ok(result.includes('-deadlock'));
        assert.ok(result.includes('-nowarning'));
    });

    test('Allows to change coverage in TLC options', async () => {
        const result = await buildTlcOptions(
            '/path/to/module.tla',
            '/path/to/module.cfg',
            ['-deadlock', '-coverage', '2', '-nowarning']
        );
        assert.strictEqual(result[0], 'module.tla');
        assert.strictEqual(result[1], '-tool');
        assert.strictEqual(result[2], '-modelcheck');
        assert.strictEqual(result[3], '-config');
        assert.strictEqual(result[4], '/path/to/module.cfg');
        assert.ok(result.includes('-deadlock'));
        assert.ok(result.includes('-coverage'));
        const coverageIdx = result.indexOf('-coverage');
        assert.strictEqual(result[coverageIdx + 1], '2');
        assert.ok(result.includes('-nowarning'));
    });

    test('Supports the specName variable in TLC options', async () => {
        const result = await buildTlcOptions(
            '/path/to/foo.tla',
            '/path/to/bar.cfg',
            ['-dump', 'dot', '${specName}.dot']
        );
        assert.strictEqual(result[0], 'foo.tla');
        assert.ok(result.includes('-dump'));
        const dumpIdx = result.indexOf('-dump');
        assert.strictEqual(result[dumpIdx + 1], 'dot');
        assert.strictEqual(result[dumpIdx + 2], 'foo.dot');
    });

    test('Supports the modelName variable in TLC options', async () => {
        const result = await buildTlcOptions(
            '/path/to/foo.tla',
            '/path/to/bar.cfg',
            ['-dump', 'dot', '${modelName}.dot']
        );
        assert.strictEqual(result[0], 'foo.tla');
        assert.ok(result.includes('-dump'));
        const dumpIdx = result.indexOf('-dump');
        assert.strictEqual(result[dumpIdx + 1], 'dot');
        assert.strictEqual(result[dumpIdx + 2], 'bar.dot');
    });

    test('Strips .tla extension from modelName when CONFIG is embedded (regression for #483)', async () => {
        const result = await buildTlcOptions(
            '/path/to/HourClock.tla',
            '/path/to/HourClock.tla',
            ['-dump', 'dot,colorize,actionlabels', '${modelName}.dot']
        );
        assert.strictEqual(result[0], 'HourClock.tla');
        assert.ok(result.includes('-dump'));
        const dumpIdx = result.indexOf('-dump');
        assert.strictEqual(result[dumpIdx + 1], 'dot,colorize,actionlabels');
        assert.strictEqual(result[dumpIdx + 2], 'HourClock.dot',
            'modelName should expand to HourClock.dot, not HourClock.tla.dot');
    });

    test('Strips .tla extension from specName when CONFIG is embedded', async () => {
        const result = await buildTlcOptions(
            '/path/to/HourClock.tla',
            '/path/to/HourClock.tla',
            ['-dump', 'dot', '${specName}.dot']
        );
        assert.strictEqual(result[0], 'HourClock.tla');
        assert.ok(result.includes('-dump'));
        const dumpIdx = result.indexOf('-dump');
        assert.strictEqual(result[dumpIdx + 1], 'dot');
        assert.strictEqual(result[dumpIdx + 2], 'HourClock.dot',
            'specName should expand to HourClock.dot, not HourClock.tla.dot');
    });

    test('Provides default classpath and GC in Java options', async () => {
        assert.deepEqual(
            buildJavaOptions(
                [], '/path/tla2tools.jar'
            ), [
                '-cp',
                '/path/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]);
    });

    test('Adds custom Java options', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-Xmx2048M', '-Xms512M'],
                '/path/to/tla2tools.jar'
            ), [
                '-Xmx2048M',
                '-Xms512M',
                '-cp',
                '/path/to/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Allows to change default GC via Java options', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-Xmx2048M', '-XX:+UseG1GC', '-Xms512M'],
                '/path/to/tla2tools.jar'
            ), [
                '-Xmx2048M',
                '-XX:+UseG1GC',
                '-Xms512M',
                '-cp',
                '/path/to/tla2tools.jar'
            ]
        );
    });

    test('Allows to add custom libraries to classpath via -cp', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'CommunityModules.jar' + path.delimiter + 'Foo.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                'CommunityModules.jar' + path.delimiter + 'Foo.jar' + path.delimiter + '/default/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Allows to add custom libraries to classpath via -classpath', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-classpath', 'Foo.jar' + path.delimiter + 'Bar.jar'],
                '/default/tla2tools.jar'
            ), [
                '-classpath',
                'Foo.jar' + path.delimiter + 'Bar.jar' + path.delimiter + '/default/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Substitutes path to tla2tools.jar if a custom one is provided', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'Foo.jar' + path.delimiter + '/custom/tla2tools.jar' + path.delimiter + 'Bar.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                'Foo.jar' + path.delimiter + '/custom/tla2tools.jar' + path.delimiter + 'Bar.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Merges classpath when many custom options are provided', async () => {
        assert.deepEqual(
            buildJavaOptions(
                [
                    '-Xmx2048M',
                    '-classpath',
                    'Foo.jar' + path.delimiter + 'Baz.jar',
                    '-XX:+UseG1GC'
                ],
                '/default/tla2tools.jar'
            ), [
                '-Xmx2048M',
                '-classpath',
                'Foo.jar' + path.delimiter + 'Baz.jar' + path.delimiter + '/default/tla2tools.jar',
                '-XX:+UseG1GC'
            ]
        );
    });

    test('Doesn\'t treat any library with a similar name as a tla2tool.jar reference', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'not_tla2tools.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                'not_tla2tools.jar' + path.delimiter + '/default/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Finds tla2tools.jar in classpath when no full path is provided', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'tla2tools.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                'tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Ignores classpath option without value', async () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp'],
                '/default/tla2tools.jar'
            ), [
                '-cp',      // We don't remove this one, user must fix the problem himself after JVM issues an error
                '-cp',
                '/default/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Splits empty command line into an empty array', async () => {
        assert.deepEqual(splitArguments(''), []);
    });

    test('Splits blank command line into an empty array', async () => {
        assert.deepEqual(splitArguments('   '), []);
    });

    test('Splits simple command line with extra spaces', async () => {
        assert.deepEqual(
            splitArguments('-a b'),
            ['-a', 'b']
        );
    });

    test('Splits command line with extra spaces', async () => {
        assert.deepEqual(
            splitArguments('  -foo   -bar    value   '),
            ['-foo', '-bar', 'value']
        );
    });

    test('Handles empty strings as command line arguments', async () => {
        assert.deepEqual(
            splitArguments('-foo ""'),
            ['-foo', '']
        );
    });

    test('Handles arguments with spaces', async () => {
        assert.deepEqual(
            splitArguments('-cp "c:\\Program Files\\MyApp\\my.jar"'),
            ['-cp', 'c:\\Program Files\\MyApp\\my.jar']
        );
    });

    test('Handles single-quoted arguments', async () => {
        assert.deepEqual(
            splitArguments("-cp 'c:\\Program Files\\My App\\my.jar' '-foo'"),
            ['-cp', 'c:\\Program Files\\My App\\my.jar', '-foo']
        );
    });

    test('Preserves spaces in command line arguments', async () => {
        assert.deepEqual(
            splitArguments('-foo "     " \'   \''),
            ['-foo', '     ', '   ']
        );
    });

    test('Adds -dumptrace for BFS mode', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', []);
        const dumpIndex = result.indexOf('-dumptrace');
        assert.notStrictEqual(dumpIndex, -1, '-dumptrace should be present for BFS mode');
        assert.strictEqual(result[dumpIndex + 1], 'tlc', 'dumptrace format should be tlc');
        const traceFilePath = result[dumpIndex + 2];
        assert.ok(traceFilePath.includes('module_trace_'), 'trace filename should contain module_trace_');
        assert.ok(traceFilePath.includes('_Mbfs.tlc'), 'trace filename should end with _Mbfs.tlc');
        assert.ok(traceFilePath.includes('_F'), 'trace filename should include fingerprint');
        assert.ok(traceFilePath.includes('_W'), 'trace filename should include workers');
        assert.ok(traceFilePath.includes('_T'), 'trace filename should include timestamp');
    });

    test('Does not add -dumptrace for simulation mode', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-simulate']);
        assert.strictEqual(result.indexOf('-dumptrace'), -1, '-dumptrace should not be present for simulation mode');
    });

    test('Does not add -dumptrace when loading trace', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-loadtrace', '/path/to/trace.tlc']);
        assert.strictEqual(result.indexOf('-dumptrace'), -1, '-dumptrace should not be present when loading trace');
    });

    test('Does not add -dumptrace when loading trace with capital letters', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-loadTrace', '/path/to/trace.tlc']);
        assert.strictEqual(result.indexOf('-dumptrace'), -1, '-dumptrace should not be present when loading trace (case insensitive)');
    });

    test('Does not add -dumptrace for simulation mode with capital letters', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-Simulate']);
        assert.strictEqual(result.indexOf('-dumptrace'), -1, '-dumptrace should not be present for simulation mode (case insensitive)');
    });

    test('Does not add -dumptrace for simulation mode with -SIMULATE', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-SIMULATE']);
        assert.strictEqual(result.indexOf('-dumptrace'), -1, '-dumptrace should not be present for simulation mode (all caps)');
    });

    test('Uses custom -fp value in trace filename', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-fp', '42']);
        const dumpIndex = result.indexOf('-dumptrace');
        assert.notStrictEqual(dumpIndex, -1, '-dumptrace should be present');
        const traceFilePath = result[dumpIndex + 2];
        assert.ok(traceFilePath.includes('_F42_'), 'trace filename should contain custom fp value');
    });


    test('Uses custom -workers value in trace filename', async () => {
        const result = await buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-workers', '4']);
        const dumpIndex = result.indexOf('-dumptrace');
        assert.notStrictEqual(dumpIndex, -1, '-dumptrace should be present');
        const traceFilePath = result[dumpIndex + 2];
        assert.ok(traceFilePath.includes('_W4_'), 'trace filename should contain custom workers value');
    });

    test('Trace filename includes spec name', async () => {
        const result = await buildTlcOptions('/path/to/MySpec.tla', '/path/to/MySpec.cfg', []);
        const dumpIndex = result.indexOf('-dumptrace');
        assert.notStrictEqual(dumpIndex, -1, '-dumptrace should be present');
        const traceFilePath = result[dumpIndex + 2];
        assert.ok(traceFilePath.includes('MySpec_trace_'), 'trace filename should start with spec name');
    });

    test('Extracts fingerprint from trace filename', async () => {
        const traceFile = '/path/to/.vscode/tlc/MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc';
        const fp = extractFingerprintFromTrace(traceFile);
        assert.strictEqual(fp, 42, 'Should extract fingerprint 42');
    });

    test('Extracts fingerprint from trace filename with different values', async () => {
        const traceFile = '/path/to/.vscode/tlc/Spec_trace_T2024-12-31_23-59-59_F127_W4_Mbfs.tlc';
        const fp = extractFingerprintFromTrace(traceFile);
        assert.strictEqual(fp, 127, 'Should extract fingerprint 127');
    });

    test('Returns undefined for invalid trace filename', async () => {
        const traceFile = '/path/to/invalid_file.tlc';
        const fp = extractFingerprintFromTrace(traceFile);
        assert.strictEqual(fp, undefined, 'Should return undefined for invalid filename');
    });

    test('Returns undefined for trace filename without fingerprint', async () => {
        const traceFile = '/path/to/.vscode/tlc/MySpec_trace_T2024-01-15_10-30-00_W1_Mbfs.tlc';
        const fp = extractFingerprintFromTrace(traceFile);
        assert.strictEqual(fp, undefined, 'Should return undefined when fingerprint is missing');
    });
});
