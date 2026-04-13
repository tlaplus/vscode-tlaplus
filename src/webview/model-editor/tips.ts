
/* eslint-disable max-len */
export const TIPS = {
    behaviorSpec: 'Choose how TLC explores your system. This tells TLC where to start and how states evolve over time.',
    mode: 'Init/Next is the most common. provide an initial-state predicate and a next-state relation. Temporal formula uses a single operator like Spec that combines fairness conditions. No behavior spec lets you evaluate constant expressions without state exploration.',
    deadlock: 'When enabled, TLC verifies every reachable state has at least one successor. Disable this if your spec intentionally has terminal states (e.g. a protocol that completes).',
    invariants: 'State predicates that must hold in every reachable state. Use these to catch safety violations. for example, TypeOK to verify variables stay within expected types.',
    properties: 'Temporal formulas checked over the full behavior graph. Use these for liveness properties. for example, verifying that every request eventually gets a response.',
    constants: 'TLC needs concrete values for each CONSTANT in your spec. Use ordinary assignment for expressions like 1..3, model value for unique identifiers, or set of model values for finite enumerated sets.',
    stateConstraint: 'Limits which states TLC explores by requiring this expression to be TRUE. Use this to make large or infinite models tractable. for example, Len(queue) < 5 to cap queue size during exploration.',
    actionConstraint: 'Filters which transitions TLC considers by requiring this expression over current and next-state variables to be TRUE. Useful for focusing model checking on specific scenarios. for example, only exploring paths where message count stays bounded.',
    defOverrides: 'Replaces spec operators with model-specific definitions during checking. Essential for making infinite sets finite. for example, overriding Nat with 0..10 so TLC can enumerate values.',
    additionalDefs: 'Extra TLA+ definitions added to the MC module. Use this for helper operators needed by constraints or overrides, or for ASSUME statements that validate model parameters.',
    symmetry: 'Declares a symmetry set to reduce the state space. TLC treats all permutations of the set as equivalent, which can dramatically speed up checking when the spec is symmetric in those values.',
    viewExpr: 'A TLA+ expression evaluated in each state and included in error traces. Use this to see computed values (like queue lengths or message counts) alongside raw state variables in counterexamples.',
    alias: 'An operator that renames or transforms variables in error traces. Useful for making counterexamples more readable. for example, showing derived values instead of raw state.',
    postCondition: 'An operator evaluated after model checking finishes. It receives the set of all reachable states, useful for computing statistics or asserting global properties of the state graph.',
    tlcOptions: 'Controls how TLC runs: checking strategy, parallelism, and diagnostics. These are command-line arguments, not part of the .cfg file.',
    checkingMode: 'BFS (breadth-first) explores all states and finds the shortest counterexamples. DFID uses less memory for very large state spaces. Simulation generates random behaviors and is useful for quick smoke tests or exploring specs that are too large to check exhaustively.',
    workers: 'Number of parallel threads. Set to 0 to automatically use all available CPU cores (recommended). More workers check faster but use more memory.',
    dfidDepth: 'Maximum search depth for depth-first iterative deepening. Deeper values explore more of the state space but take longer.',
    simTraces: 'How many random traces to generate. Set to 0 for unlimited (runs until you stop it). Higher values give more confidence but take longer.',
    simSeed: 'A fixed seed makes simulation reproducible. the same seed always generates the same traces. Useful for debugging a specific counterexample.',
    fpBits: 'Controls the fingerprint function used to identify states. Higher values reduce the probability of hash collisions (false matches) but use more memory. The default of 1 is fine for most models.',
    profiling: 'Shows how often each expression is evaluated during model checking. Useful for finding performance bottlenecks in your spec. results appear in the TLC coverage panel.',
};
/* eslint-enable max-len */
