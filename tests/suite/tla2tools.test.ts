import * as assert from 'assert';
import * as path from 'path';
import { buildJavaOptions, buildTlcOptions, buildPlusCalOptions } from '../../src/tla2tools';

suite('TLA+ Tools Test Suite', () => {

    test('Builds PlusCal options with no custom settings', () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', []),
            ['module.tla']
        );
    });

    test('Puts PlusCal custom options before module name', () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', ['-lineWidth', '100', '-nocfg']),
            ['-lineWidth', '100', '-nocfg', 'module.tla']
        );
    });

    test('Provides default TLC options', () => {
        assert.deepEqual(
            buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', []),
            ['module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/module.cfg']
        );
    });

    test('Adds custom TLC options', () => {
        assert.deepEqual(
            buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-deadlock', '-checkpoint', '5']),
            ['module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/module.cfg',
            '-deadlock', '-checkpoint', '5']
        );
    });

    test('Allows to change module .cfg in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/module.tla',
                '/path/to/module.cfg',
                ['-deadlock', '-config', '/path/to/another.cfg', '-nowarning']
            ), [
                'module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/another.cfg',
                '-deadlock', '-nowarning'
            ]
        );
    });

    test('Allows to change coverage in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/module.tla',
                '/path/to/module.cfg',
                ['-deadlock', '-coverage', '2', '-nowarning']
            ), [
                'module.tla', '-tool', '-modelcheck', '-coverage', '2', '-config', '/path/to/module.cfg',
                '-deadlock', '-nowarning'
            ]
        );
    });

    test('Supports the specName variable in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/foo.tla',
                '/path/to/bar.cfg',
                ['-dump', 'dot', '${specName}.dot']
            ), [
                'foo.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/bar.cfg',
                '-dump', 'dot', 'foo.dot'
            ]
        );
    });

    test('Supports the modelName variable in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/foo.tla',
                '/path/to/bar.cfg',
                ['-dump', 'dot', '${modelName}.dot']
            ), [
                'foo.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/bar.cfg',
                '-dump', 'dot', 'bar.dot'
            ]
        );
    });

    test('Provides default classpath and GC in Java options', () => {
        assert.deepEqual(
            buildJavaOptions(
                [], '/path/tla2tools.jar'
            ), [
                '-cp',
                '/path/tla2tools.jar',
                '-XX:+UseParallelGC'
            ]);
    });

    test('Adds custom Java options', () => {
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

    test('Allows to change default GC via Java options', () => {
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

    test('Allows to add custom libraries to classpath via -cp', () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'CommunityModules.jar' + path.delimiter + 'Foo.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                '/default/tla2tools.jar' + path.delimiter + 'CommunityModules.jar:Foo.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Allows to add custom libraries to classpath via -classpath', () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-classpath', 'Foo.jar' + path.delimiter + 'Bar.jar'],
                '/default/tla2tools.jar'
            ), [
                '-classpath',
                '/default/tla2tools.jar' + path.delimiter + 'Foo.jar' + path.delimiter + 'Bar.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Substitutes path to tla2tools.jar if a custom one is provided', () => {
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

    test('Merges classpath when many custom options are provided', () => {
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
                '/default/tla2tools.jar' + path.delimiter + 'Foo.jar' + path.delimiter + 'Baz.jar',
                '-XX:+UseG1GC'
            ]
        );
    });

    test('Doesn\'t treat any library with a similar name as a tla2tool.jar reference', () => {
        assert.deepEqual(
            buildJavaOptions(
                ['-cp', 'not_tla2tools.jar'],
                '/default/tla2tools.jar'
            ), [
                '-cp',
                '/default/tla2tools.jar' + path.delimiter + 'not_tla2tools.jar',
                '-XX:+UseParallelGC'
            ]
        );
    });

    test('Finds tla2tools.jar in classpath when no full path is provided', () => {
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

    test('Ignores classpath option without value', () => {
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
});
