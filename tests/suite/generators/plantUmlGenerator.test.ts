import * as assert from 'assert';
import { traceDataToPlantUml } from '../../../src/generators/plantUmlGenerator';
import { TraceData, TraceMessage, TraceStep, ConcurrentStep, ChannelStyle } from '../../../src/webview/sequenceDiagram/types';

/** Helper: minimal TraceData with defaults. */
function makeTraceData(overrides: Partial<TraceData> & { trace: TraceMessage[] }): TraceData {
    return {
        parameters: {},
        participants: [],
        ...overrides,
    };
}

suite('PlantUML Generator Test Suite', () => {

    test('Produces @startuml and @enduml delimiters', () => {
        const data = makeTraceData({
            participants: ['A', 'B'],
            trace: [{ msg: 'Req', src: 'A', dst: 'B' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.startsWith('@startuml'));
        assert.ok(puml.trimEnd().endsWith('@enduml'));
    });

    test('Declares all participants in order', () => {
        const data = makeTraceData({
            participants: ['CPU', 'LLC', 'MEM'],
            trace: [{ msg: 'R', src: 'CPU', dst: 'LLC' }],
        });
        const puml = traceDataToPlantUml(data);
        const cpuIdx = puml.indexOf('participant "CPU"');
        const llcIdx = puml.indexOf('participant "LLC"');
        const memIdx = puml.indexOf('participant "MEM"');
        assert.ok(cpuIdx >= 0, 'CPU should be declared');
        assert.ok(llcIdx >= 0, 'LLC should be declared');
        assert.ok(memIdx >= 0, 'MEM should be declared');
        assert.ok(cpuIdx < llcIdx, 'CPU before LLC');
        assert.ok(llcIdx < memIdx, 'LLC before MEM');
    });

    test('Declares participants with sanitized aliases', () => {
        const data = makeTraceData({
            participants: ['My-Agent 1'],
            trace: [{ msg: 'R', src: 'My-Agent 1', dst: 'My-Agent 1' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('participant "My-Agent 1" as My_Agent_1'));
    });

    test('Renders sequential messages as arrows', () => {
        const data = makeTraceData({
            participants: ['A', 'B'],
            trace: [
                { msg: 'Req', src: 'A', dst: 'B' },
                { msg: 'Ack', src: 'B', dst: 'A' },
            ],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('A'));
        assert.ok(puml.includes('B'));
        // Both messages should appear
        assert.ok(puml.includes('Req'));
        assert.ok(puml.includes('Ack'));
    });

    test('Includes autonumber', () => {
        const data = makeTraceData({
            participants: ['A', 'B'],
            trace: [{ msg: 'R', src: 'A', dst: 'B' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('autonumber'));
    });

    test('Renders parameters as header', () => {
        const data = makeTraceData({
            parameters: { model: 'MESI', writers: '2' },
            participants: ['A'],
            trace: [{ msg: 'R', src: 'A', dst: 'A' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('header'));
        assert.ok(puml.includes('model=MESI'));
        assert.ok(puml.includes('writers=2'));
    });

    test('No header when parameters are empty', () => {
        const data = makeTraceData({
            parameters: {},
            participants: ['A'],
            trace: [{ msg: 'R', src: 'A', dst: 'A' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(!puml.includes('header'));
    });

    test('Applies channel colors to arrows and labels', () => {
        const styles: Record<string, ChannelStyle> = {
            'data': { stroke: '#e53935', label: '#c62828', name: 'Data Channel' },
        };
        const data = makeTraceData({
            participants: ['A', 'B'],
            trace: [{ msg: 'Write', src: 'A', dst: 'B', ch: 'data' }],
            channelStyles: styles,
        });
        const puml = traceDataToPlantUml(data);
        // Arrow should contain color
        assert.ok(puml.includes('#e53935') || puml.includes('e53935'),
            'Arrow should use channel stroke color');
        // Label should include channel name
        assert.ok(puml.includes('Data Channel'));
    });

    test('Renders concurrent steps with par/group blocks', () => {
        const concurrentStep: ConcurrentStep = {
            concurrent: [
                [{ msg: 'A', src: 'P', dst: 'Q' }],
                [{ msg: 'B', src: 'R', dst: 'S' }],
            ],
        };
        const steps: TraceStep[] = [concurrentStep];
        const data = makeTraceData({
            participants: ['P', 'Q', 'R', 'S'],
            trace: [{ msg: 'A', src: 'P', dst: 'Q' }, { msg: 'B', src: 'R', dst: 'S' }],
            steps,
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('\npar '), 'Should include par block');
        assert.ok(puml.includes('Chain 1'), 'Should label Chain 1');
        assert.ok(puml.includes('Chain 2'), 'Should label Chain 2');
        // Both chains end with 'end'
        const endCount = (puml.match(/^\s*end\s*$/gm) || []).length;
        assert.ok(endCount >= 3, `Expected at least 3 end markers (2 groups + 1 par), got ${endCount}`);
    });

    test('Single concurrent chain renders without par wrapper', () => {
        const concurrentStep: ConcurrentStep = {
            concurrent: [
                [{ msg: 'A', src: 'P', dst: 'Q' }],
            ],
        };
        const steps: TraceStep[] = [concurrentStep];
        const data = makeTraceData({
            participants: ['P', 'Q'],
            trace: [{ msg: 'A', src: 'P', dst: 'Q' }],
            steps,
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(!puml.includes('\npar '), 'Single chain should not use par block');
    });

    test('Mixed sequential and concurrent steps', () => {
        const seqStep: TraceMessage[] = [{ msg: 'Init', src: 'A', dst: 'B' }];
        const concStep: ConcurrentStep = {
            concurrent: [
                [{ msg: 'X', src: 'C', dst: 'D' }],
                [{ msg: 'Y', src: 'E', dst: 'F' }],
            ],
        };
        const seqStep2: TraceMessage[] = [{ msg: 'Done', src: 'B', dst: 'A' }];
        const steps: TraceStep[] = [seqStep, concStep, seqStep2];
        const data = makeTraceData({
            participants: ['A', 'B', 'C', 'D', 'E', 'F'],
            trace: [],
            steps,
        });
        const puml = traceDataToPlantUml(data);
        // Init should appear before par
        const initIdx = puml.indexOf('Init');
        const parIdx = puml.indexOf('\npar ');
        const doneIdx = puml.indexOf('Done');
        assert.ok(initIdx < parIdx, 'Init before par');
        assert.ok(parIdx < doneIdx, 'par before Done');
    });

    test('Handles dashed arrow style', () => {
        const data = makeTraceData({
            participants: ['A', 'B'],
            trace: [{ msg: 'DashMsg', src: 'A', dst: 'B', line: 'dashed' }],
            channelStyles: { 'ch1': { stroke: '#e53935', label: '#c62828', name: 'Ch1' } },
        });
        // Assign channel to trigger style path
        data.trace[0].ch = 'ch1';
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('dashed'), 'Should include dashed style in arrow');
    });

    test('Includes skinparam settings', () => {
        const data = makeTraceData({
            participants: ['A'],
            trace: [{ msg: 'R', src: 'A', dst: 'A' }],
        });
        const puml = traceDataToPlantUml(data);
        assert.ok(puml.includes('skinparam backgroundColor transparent'));
        assert.ok(puml.includes('skinparam defaultFontSize 12'));
    });
});
