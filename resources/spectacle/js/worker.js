// TODO: Just a skeleton here.

console.log("Worker is running...")

self.importScripts('tree-sitter.js');
self.importScripts('eval.js');
self.importScripts('lib/lodash.min.js');
self.importScripts('hash-sum/hash-sum.js');

let parser;
let languageName = "tlaplus";
let enableEvalTracing = false;

// Compute a hash of a quantifier bounds objects, which should be simply a
// mapping from identifier strings to TLA values.
function hashQuantBounds(quantBounds){
    let keysSorted = _.keys(quantBounds).sort();
    let kvPairs = keysSorted.map(k => [k, quantBounds[k].fingerprint()]);
    return hashSum(kvPairs);
}

function actionIdForNextState(currNextStates, nextStateHash) {
    // Find the action id that corresponds to the selected next state.
    console.log("currNextStates:", currNextStates);
    // console.log("nextStateHash:", _.find(currNextStates, (s) => s["state"].fingerprint() === nextStateHash));
    let actionId = _.findKey(currNextStates, (states) => _.find(states, (s) => s["state"].fingerprint() === nextStateHash));
    console.log("actionId:", actionId);
    return actionId;
}

function recomputeNextStates(model,fromState) {
    let interp = new TlaInterpreter();
    let nextStates;

    evalNodeGraphsPerAction = {};

    // Compute next states broken down by action.
    // TODO: Consider if this functionality more appropriately lives inside the interpreter logic.
    if (model.actions.length > 1) {
        let nextStatesByAction = {}
        for (const action of model.actions) {
            assert(action instanceof TLAAction);
            // console.log("FROM:", fromState)
            const start = performance.now();
            cloneTime = 0;
            numClones = 0;

            console.log("fromState:", fromState);
            console.log("actions:", model.actions);
            console.log("actions:", model.specTreeObjs);
            let nextStatesForAction = interp.computeNextStates(model.specTreeObjs, model.specConstVals, [fromState], action.node, model.spec, model.nextDefName, model.definitionOverrides)
            console.log("nextStatesForAction", nextStatesForAction); 

            nextStatesForAction = nextStatesForAction.map(c => {
                let deprimed = c["state"].deprimeVars();
                return { "state": deprimed, "quant_bound": c["quant_bound"] };
            });
            // nextStatesForActionQuantBound = nextStatesForActionQuantBound.map(c => c["quant_bound"]);
            nextStatesByAction[action.id] = nextStatesForAction;

            evalNodeGraphsPerAction[action.id] = evalNodeGraph;

            const duration = (performance.now() - start).toFixed(1);

            console.log(`Generating next states for action '${action.name}' took ${duration}ms, (${nextStatesForAction.length} distinct states generated, clone time: ${cloneTime.toFixed(2)}ms, ${numClones} clones)`)
            cloneTime = 0;
            numClones = 0;
        }
        nextStates = nextStatesByAction;
    } else {
        nextStates = interp.computeNextStates(model.specTreeObjs, model.specConstVals, [fromState], undefined, model.spec, model.nextDefName, model.definitionOverrides)
            .map(c => {
                let deprimed = c["state"].deprimeVars();
                return { "state": deprimed, "quant_bound": c["quant_bound"] };
            });
    }

    return nextStates;
}


function chooseNextState(model, statehash_short, quantBoundsHash, rethrow = false) {
    // Clear forward history since we're taking a new path
    // model.forwardHistory = [];
    // model.forwardHistoryActions = [];
    
    // console.log("currNextStates:", JSON.stringify(currNextStates));
    // console.log("chooseNextState: ", statehash_short);

    let currNextStatesSet = _.flatten(_.values(model.currNextStates));
    console.log("currNextStatesSet:", currNextStatesSet);
    let nextStateChoices = currNextStatesSet.filter(s => {
        if (quantBoundsHash === undefined || _.isEmpty(quantBoundsHash)) {
            console.log("s:", s["state"]);
            return s["state"].fingerprint() === statehash_short;
        } else {
            // If quant bounds are given, then choose next state that both
            // matches state hash and also matches the quant bounds hash. This
            // can matter when, for example, two distinct actions (e.g. those
            // with different parameters) lead to the same state.
            let sameQuantParams = _.isEqual(hashQuantBounds(s["quant_bound"]), quantBoundsHash);
            return s["state"].fingerprint() === statehash_short && sameQuantParams;
        }
    });

    let nextStateActionId = null;
    if (model.actions.length > 1 && model.currTrace.length >= 1) {
        nextStateActionId = actionIdForNextState(model.currNextStates, statehash_short)
        // console.log("actionid:", nextStateActionId);
    }

    if (nextStateChoices.length === 0) {
        throw Error("Given state hash " + statehash_short + " does not exist among possible next states.")
    }
    let nextState = nextStateChoices[0];

    // Append next state to the trace and update current route.
    model.currTrace.push([nextState.state, nextStateActionId, quantBoundsHash, nextState["quant_bound"]] );

    // Recrod the quant bounds used in the action as well in case we need to tell between two different actions
    // with the same type but different params that lead to the same state.
    
    model.currTraceActions.push([nextStateActionId, quantBoundsHash]);
    // updateTraceRouteParams();

    const start = performance.now();

    try {
        console.log("recomputing next states for", nextState["state"]);
        let nextStates = recomputeNextStates(model, nextState["state"]);
        const duration = (performance.now() - start).toFixed(1);

        const start2 = performance.now();
        model.currNextStates = _.cloneDeep(nextStates);
        const duration2 = (performance.now() - start2).toFixed(1);

        console.log(`Generating next states took ${duration}ms (cloning took ${duration2}ms )`)
    } catch (e) {
        console.error("Error computing next states.", e);
        if (currEvalNode !== null) {
            // Display line where evaluation error occurred.
            // showEvalError(currEvalNode, e);
        }
        if(rethrow){
            throw e;
        }
        return;
    }

    return nextState;
}


onmessage = async (e) => {


    let action = e.data.action;
    let newText = e.data.newText;
    let specPath = e.data.specPath;
    let constValInputs = e.data.constValInputs;
    let invariantExpr = e.data.invariantExpr;
    let initDefName = e.data.initDefName;
    let nextDefName = e.data.nextDefName;
    let definitionOverrides = e.data.definitionOverrides;

    await TreeSitter.init();
    parser = new TreeSitter();

    let tree = null;
    var ASSIGN_PRIMED = false;


    // Load the tree-sitter TLA+ parser.
    let language;
    LANGUAGE_BASE_URL = "js";
    const url = `tree-sitter-${languageName}.wasm`;
    try {
        console.log("Loading language from", url);
        language = await TreeSitter.Language.load(url);
    } catch (e) {
        console.error(e);
        return;
    }

    tree = null;
    parser.setLanguage(language);

    console.log("Message received from main script");
    const workerResult = `Result: ${e.data}`;
    console.log(e.data);
    console.log("Posting message back to main script");

    let spec = new TLASpec(newText, specPath);
    return spec.parse().then(function(){
        console.log("SPEC WAS PARSED IN WEBWORKER.", spec);

        let constVals = {};
        let constTlaVals = {};
        let model = {};

        model.spec = spec;
        model.specText = newText;
        model.specTreeObjs = spec.spec_obj;
        model.errorObj = null;
        model.nextDefName = nextDefName;
        model.initDefName = initDefName;
        model.definitionOverrides = definitionOverrides;

        let nextDef = model.spec.getDefinitionByName(model.nextDefName);
        model.actions = spec.parseActionsFromNode(nextDef["node"]);

        // Evaluate each CONSTANT value expression.
        for (var constDecl in constValInputs) {
            let constValText = constValInputs[constDecl];

            if (constValText === undefined) {
                throw "no constant value given for " + constDecl;
            }
            // console.log("constDecl:", constDecl, constValText);
            constVals[constDecl] = constValText;

            model.specDefs = spec.spec_obj["op_defs"]
    
            let ctx = new Context(null, new TLAState({}), model.specDefs, {}, constTlaVals);
            // Flag so that we treat unknown identifiers as model values during evaluation.
            ctx.evalModelVals = true;
            let cVal = evalExprStrInContext(ctx, constValText);
            // console.log("cval:", cVal);
            constTlaVals[constDecl] = cVal;
        }
    
        // console.log("constTlaVals:", constTlaVals);
        model.specConstVals = constTlaVals;
        model.currTrace = [];
        model.currTraceActions = [];
        model.currNextStates = [];

        // Re-execute a trace from a list of given state hashes.
        if(action === "loadTrace"){
            let hashTrace = e.data.stateHashList;

            try {
                // Generate initial states.
                let interp = new TlaInterpreter();

                let initStates = interp.computeInitStates(spec.spec_obj, constTlaVals, true, spec, model.initDefName, model.definitionOverrides);
                console.log("initStates:", initStates);
                model.currNextStates = initStates;

                let trace = [];
                let totalSteps = hashTrace.length;

                for (let i = 0; i < hashTrace.length; i++) {
                    let stateHash = hashTrace[i];
                    console.log("stateHash:", stateHash);
                    
                    // Check each state for possible quant bounds hash
                    let stateAndQuantBounds = stateHash.split("_");
                    let rethrow = true;
                    let stateInfo = {
                        hash: stateHash
                    };

                    let nextState = null;

                    try {
                        if (stateAndQuantBounds.length > 1) {
                            let justStateHash = stateAndQuantBounds[0];
                            let quantBoundHash = stateAndQuantBounds[1];
                            nextState = chooseNextState(model, justStateHash, quantBoundHash, rethrow);
                            stateInfo.hash = justStateHash;
                            stateInfo.quantBoundsHash = quantBoundHash;
                        } else {
                            nextState = chooseNextState(model, stateHash, undefined, rethrow);
                        }
                        stateInfo.state = nextState.state;
                        stateInfo.actionId = nextState["actionId"];
                        trace.push(stateInfo);
                    } catch (err) {
                        console.error("Error loading state", err);
                        postMessage({
                            type: "error",
                            error: `Error loading state ${i + 1}/${totalSteps}: ${err.message}`
                        });
                        return;
                    }

                    // Send progress update
                    postMessage({
                        type: "progress",
                        currentState: i + 1,
                        totalStates: totalSteps
                    });
                }

                console.log("model.currTrace:", model.currTrace);

                // Send completion message with trace info
                postMessage({
                    type: "complete",
                    trace: model.currTrace,
                    currTraceActions: model.currTraceActions
                });

            } catch (err) {
                console.error("Error initializing trace loading:", err);
                postMessage({
                    type: "error", 
                    error: `Error initializing trace loading: ${err.message}`
                });
            }

            return;
        }


        // Generate initial states.
        let interp = new TlaInterpreter();

        let start = performance.now();
        let reachableStates = interp.computeReachableStates(spec.spec_obj, constTlaVals, invariantExpr, spec, logMetricsInterval=200);
        const duration = (performance.now() - start).toFixed(1);
        console.log("Reachable states from WebWorker.", reachableStates, `duration: ${duration}ms`);
        console.log(`Computed ${reachableStates.states.length} reachable states in ${duration}ms.`);

        if(!reachableStates.invHolds){
            postMessage(reachableStates);
            return;
        }

        // Seems it is fine to serialize TLAState objects back through the web worker.
        postMessage(reachableStates);
        return;


    }).catch(function(e){
        console.log("Error parsing and loading spec.", e);
        // model.errorObj = {parseError: true, obj: e, message: "Error parsing spec."};
    });

};