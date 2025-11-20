/**
 * 
 * TLA+ interpreter. 
 * 
 * Contains logic for expression evaluation and initial/next state generation. 
 * See the `evalExpr` function below.
 * 
 */

// For debugging.
let depth = 0;
let cloneTime = 0.0;
let numClones = 0;
const TLA_STANDARD_MODULES = [
    "TLC",
    "TLCExt",
    "FiniteSets",
    "Sequences",
    "Integers",
    "Bags",
    "Naturals",
    "Reals",
    "Randomization"
]

// Some hard-coded modules which can be found in TLA+ CommunityModules repo:
// https://github.com/tlaplus/CommunityModules/blob/master/modules
const TLA_COMMUNITY_MODULES = [
    "BagsExt",
    "Bitwise",
    "Combinatorics",
    "FiniteSetsExt",
    "Folds",
    "Functions",
    "Graphs",
    "Relation",
    "SequencesExt",
    "UndirectedGraphs",
    "SVG",
    "IOUtils"
]

const TLA_COMMUNITY_MODULES_BASE_URL = "https://raw.githubusercontent.com/tlaplus/CommunityModules/master/modules";

// Simple assertion utility.
function assert(condition, message) {
    if (!condition) {
        console.error("assertion failed");
        if (message) {
            console.error(message);
        }
        throw new Error(message || 'Assertion failed');
    }
}
function evalLog(...msgArgs) {
    if (enableEvalTracing) {
        let indent = "(L" + depth + ")" + ("|".repeat(depth * 2));
        let args = [indent].concat(msgArgs)
        console.log(...args);
    }
}

function cartesianProductOf() {
    return _.reduce(arguments, function (a, b) {
        return _.flatten(_.map(a, function (x) {
            return _.map(b, function (y) {
                return x.concat([y]);
            });
        }), true);
    }, [[]]);
}

function subsets(vals) {
    const powerset = [];
    generatePowerset([], 0);

    function generatePowerset(path, index) {
        powerset.push(path);
        for (let i = index; i < vals.length; i++) {
            generatePowerset([...path, vals[i]], i + 1);
        }
    }

    return powerset;
}

// Combinations with replacement.
// See: https://stackoverflow.com/questions/32543936/combination-with-repetition
function combinations(arr, l) {
    if (l === void 0) l = arr.length; // Length of the combinations
    var data = Array(l),             // Used to store state
        results = [];                // Array of results
    (function f(pos, start) {        // Recursive function
        if (pos === l) {                // End reached
            results.push(data.slice());  // Add a copy of data to results
            return;
        }
        for (var i = start; i < arr.length; ++i) {
            data[pos] = arr[i];          // Update data
            f(pos + 1, i);                 // Call f recursively
        }
    })(0, 0);                        // Start at index 0
    return results;                  // Return results
}

function hashState(stateObj) {
    return hashSum(stateObj);
}


// Meant to represent an abstract node in the expression evaluation tree.
// Can be evaluated on inputs and produces outputs that can then feed into
// other eval nodes.
class AbstractEvalNode {
    constructor(name, type, children) {
        this.name = name;
        this.type = type;
        this.children = children;
    }
}

//
//
// TLA+ Value type definitions.
//
//

class TLAValue {
    constructor() {
    }

    toJSON() {
        return "'toJSON' unimplemented";
    }

    // This is notably useful for deserializing values from JSON objects that
    // are produced as a result of `structuredClone` calls on class instances
    // (e.g. when passing objects back from a WebWorker).
    static fromJSON(jsonval) {
        if (jsonval.type === "IntValue") {
            return IntValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "StringValue") {
            return StringValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "BoolValue") {
            return BoolValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "FcnRcdValue") {
            return FcnRcdValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "SetValue") {
            return SetValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "TupleValue") {
            return TupleValue.fromJSON(jsonval);
        }
        else if (jsonval.type === "ModelValue") {
            return ModelValue.fromJSON(jsonval);
        } else{
            throw new Error("Unknown value type: " + jsonval.type);
        }
    }

    toJSONITF() {
        return "'toJSONITF' unimplemented";
    }

    fingerprint() {
        return "no_fingerprint";
    }

    /**
     * Check if this value is equal to the value 'other'.
     * @param {TLAValue} other 
     */
    equals(other) {
        throw new Exception("equality check unimplemented!");
    }

    /**
     * Convert value to tuple, if possible.
     */
    toTuple() {
        console.error("toTuple: value cannot be converted to tuple");
        throw "value cannot be converted to tuple";
    }
}

// Lazy value. Currently unused but may be utilized in future.
class LazyValue extends TLAValue {
    constructor(n) {
        super(n);
        this.expr = n;
        this.context = n;
    }

    fingerprint(){
        return evalExpr(this.expr, this.context)[0]["val"].fingerprint();
    }
}

class IntValue extends TLAValue {
    constructor(n) {
        super(n);
        this.val = n;
        this.type = "IntValue";
    }
    toString() {
        return this.val.toString();
    }
    toJSON() {
        return this.val;
    }
    static fromJSON(jsonval){
        return new IntValue(jsonval.val);
    }
    toJSONITF() {
        return { "#type": "int", "#value": this.val };
    }
    getVal() {
        return this.val;
    }
    plus(other) {
        assert(other instanceof IntValue);
        return new IntValue(this.val + other.getVal())
    }
    minus(other) {
        assert(other instanceof IntValue);
        return new IntValue(this.val - other.getVal())
    }
    fingerprint() {
        return hashSum(this.val);
    }
    equals(other) {
        if (!other instanceof IntValue) {
            return false;
        } else {
            return this.val === other.getVal();
        }
    }
}

class BoolValue extends TLAValue {
    constructor(n) {
        super(n);
        this.val = n;
        this.type = "BoolValue";
    }
    toString() {
        return this.val ? "TRUE" : "FALSE";
    }
    toJSON() {
        return this.val;
    }

    static fromJSON(jsonval){
        return new BoolValue(jsonval.val);
    }

    toJSONITF() {
        return { "#type": "bool", "#value": this.val };
    }
    fingerprint() {
        return hashSum(this.val);
    }
    getVal() {
        return this.val;
    }
    and(other) {
        return new BoolValue(this.getVal() && other.getVal());
    }
}


// Basically behaves as a string value, but can be only be instantiated by CONSTANT declarations.
class ModelValue extends TLAValue {
    constructor(s) {
        super(s);
        this.val = s;
        this.type = "ModelValue";
    }
    getVal() {
        return this.val;
    }
    toString() {
        return this.val;
    }
    toJSON() {
        return this.val;
    }

    static fromJSON(jsonval){
        return new ModelValue(jsonval.val);
    }

    toJSONITF() {
        return { "#type": "modelVal", "#value": this.val };
    }
    fingerprint() {
        return this.val;
    }
}

class StringValue extends TLAValue {
    constructor(s) {
        super(s);
        this.val = s;
        this.type = "StringValue";
    }
    getVal() {
        return this.val;
    }
    toString() {
        return "\"" + this.val + "\"";
    }
    toJSON() {
        return this.val;
    }
    static fromJSON(jsonval){
        return new StringValue(jsonval.val);
    }
    toJSONITF() {
        return { "#type": "string", "#value": this.val };
    }
    fingerprint() {
        return this.val;
    }
}

class SetValue extends TLAValue {
    constructor(elems) {
        super(elems);
        // Remove duplicates at construction.
        this.elems = _.uniqBy(elems, (e) => e.fingerprint());
        this.type = "SetValue";
    }
    toString() {
        return "{" + this.elems.map(x => x.toString()).join(",") + "}";
    }

    toJSON() {
        return this.elems;
    }
    
    static fromJSON(jsonval){
        return new SetValue(jsonval.elems.map(e => TLAValue.fromJSON(e)));
    }

    toJSONITF() {
        // Do a crude normalization by sorting by stringified version of each value
        // TODO: Eventually will need a more principled way to do normalization
        // and/or equality checking.
        return {
            "#type": "set",
            "#value": _.sortBy(this.elems, (e) => e.toString()).map(el => el.toJSONITF())
        };
    }

    getElems() {
        return this.elems;
    }

    size() {
        // TODO: Need to consider duplicates. Will likely require better equality handling for all types.
        return this.elems.length;
    }

    contains(elem){
        return this.elems.some(e => e.fingerprint() === elem.fingerprint());
    }

    unionWith(otherSet) {
        return new SetValue(_.uniqWith(this.elems.concat(otherSet.getElems()), _.isEqual));
    }

    intersectionWith(otherSet) {
        return new SetValue(_.intersectionWith(this.elems, otherSet.getElems(), _.isEqual));
    }

    isSubsetOf(otherSet) {
        return new BoolValue(this.intersectionWith(otherSet).size() === this.size());
    }

    diffWith(otherSet) {
        return new SetValue(_.differenceWith(this.elems, otherSet.getElems(), _.isEqual));
    }
    fingerprint() {
        return hashSum(this.elems.map(e => e.fingerprint()).sort());
    }
}

class TupleValue extends TLAValue {
    constructor(elems) {
        super(elems);
        this.elems = elems;
        this.type = "TupleValue";
    }
    toString() {
        return "<<" + this.elems.map(x => x.toString()).join(",") + ">>";
    }

    // Tuples can be interpreted as functions with a domain over a subset of the natural numbers.
    getDomain(){
        return _.range(1, this.elems.length + 1).map(v => new IntValue(v));
    }
    
    // Tuples can be interpreted as functions with a range of values.
    getValues(){
        return this.elems;
    }

    toJSON() {
        return this.elems;
    }

    static fromJSON(jsonval){
        return new TupleValue(jsonval.elems.map(e => TLAValue.fromJSON(e)));
    }

    append(el) {
        return new TupleValue(this.elems.concat([el]));
    }

    concatTup(tup) {
        return new TupleValue(this.elems.concat(tup.getElems()));
    }

    head() {
        if (this.elems.length === 0) {
            throw new Error("Tried to get head of empty list");
        }
        return this.elems[0];
    }

    tail() {
        if (this.elems.length === 0) {
            throw new Exception("Tried to get tail of empty list");
        }
        return new TupleValue(this.elems.slice(1));
    }

    getElems() {
        return this.elems;
    }
    toJSONITF() {
        return { "#type": "tup", "#value": this.elems.map(el => el.toJSONITF()) };
    }
    fingerprint() {
        let rcd = this.toFcnRcd();
        return rcd.fingerprint();
    }

    /**
     * Return this tuple as an equivalent function value.
     */
    toFcnRcd() {
        // Tuples are functions with contiguous natural number domains.
        let domainVals = _.range(1, this.elems.length + 1).map(v => new IntValue(v));
        return new FcnRcdValue(domainVals, this.elems);
    }

    length() {
        return this.elems.length;
    }

    toTuple() {
        return this;
    }
}

class FcnRcdValue extends TLAValue {
    constructor(domain, values, isRecord) {
        super(domain, values);
        this.domain = domain;
        this.values = values
        // Trace 'record' types explicitly.
        this.isRecord = isRecord || false;
        this.type = "FcnRcdValue";
    }
    toString() {
        if (this.isRecord) {
            return "[" + this.domain.map((dv, idx) => dv.getVal() + " |-> " + this.values[idx]).join(", ") + "]";
        } else {
            return "(" + this.domain.map((dv, idx) => dv.toString() + " :> " + this.values[idx]).join(" @@ ") + ")";
        }
    }

    toJSON() {
        return _.fromPairs(_.zip(this.domain, this.values))
    }

    static fromJSON(jsonval){
        return new FcnRcdValue(
                    jsonval.domain.map(e => TLAValue.fromJSON(e)), 
                    jsonval.values.map(e => TLAValue.fromJSON(e)), 
                    jsonval.isRecord);
    }

    getDomain() {
        return this.domain;
    }

    getValues() {
        return this.values;
    }

    // Get index of function argument in the function's domain.
    argIndex(arg) {
        return _.findIndex(this.domain, (v) => {
            return v.fingerprint() === arg.fingerprint();
        });
    }

    /**
     * Apply the function to the argument 'arg'.
     */
    applyArg(arg) {
        let idx = this.argIndex(arg);
        assert(idx >= 0, "argument " + arg + " doesn't exist in function domain.");
        return this.values[idx];
    }

    /**
     * Checks whether the given argument is in the domain of the function.
     */
    argInDomain(arg){
        return this.domain.map(val => val.fingerprint()).includes(arg.fingerprint())
    }

    /**
     * Apply the function to the path argument 'arg', given as array of args e.g. ["x", "y"].
     */
    applyPathArg(pathArg) {
        if (pathArg.length === 1) {
            return this.applyArg(pathArg[0]);
        }
        // Apply head of the path arg.
        let fApplied = this.applyArg(pathArg[0])
        // Apply rest of the path arg.
        return fApplied.applyPathArg(pathArg.slice(1));

        // let idx = this.argIndex(pathArg[0]);
        // assert(idx >= 0, "argument " + arg + " doesn't exist in function domain.");
        // return this.values[idx].applyPathArg(pathArg.slice(1));
    }


    updateWith(arg, newVal) {
        let idx = this.argIndex(arg);
        let newFn = _.cloneDeep(this);
        newFn.values[idx] = newVal;
        return newFn;
    }
    // Update a record value given a key sequence, representing a nested update.
    // e.g. given ["x", "y", "z"], we make the update rcd["x"]["y"]["z"] := newVal.
    updateWithPath(args, newVal) {
        evalLog("updateWithPath args:", args);
        evalLog("updateWithPath obj:", this);

        // Base case, when the update is non-nested.
        if (args.length === 1) {
            evalLog("Hit non-nested update", args);
            let idx = this.argIndex(args[0]);
            assert(idx >= 0, "arg index wasn't found for argument " + args[0]);
            let newFn = _.cloneDeep(this);
            evalLog("newVal", newVal);
            newFn.values[idx] = newVal;
            return newFn;
        }

        // Otherwise, recursively update.
        let idx = this.argIndex(args[0]);
        let newFn = _.cloneDeep(this);
        evalLog("newFn", newFn);
        newFn.values[idx] = newFn.values[idx].updateWithPath(args.slice(1), newVal);
        return newFn;
    }

    /**
     * Compose this function with the given function value and return the result.
     * @param {FcnRcdValue} other 
     */
    compose(other) {
        assert(other instanceof FcnRcdValue);

        // [x \in (DOMAIN f) \cup (DOMAIN g) |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]]

        // Construct the new domain.
        // Take the union of the two domains, based on fingerprint equality.
        let thisDomainFps = this.domain.map(x => x.fingerprint());
        let newDomain = _.cloneDeep(this.domain);
        for (const v of other.getDomain()) {
            if (!thisDomainFps.includes(v.fingerprint())) {
                newDomain.push(v);
            }
        }

        evalLog("new domain:", newDomain);

        let newRange = [];
        // Construct the new range. If a domain value appeared in domains of both functions,
        // we prefer the range value of ourselves.
        for (const v of newDomain) {
            if (thisDomainFps.includes(v.fingerprint())) {
                // use our value.
                newRange.push(this.applyArg(v));
            } else {
                // use the other value.
                newRange.push(other.applyArg(v));
            }
        }

        return new FcnRcdValue(newDomain, newRange);
    }

    toJSONITF() {
        if (this.isRecord) {
            console.log(this.domain);
            console.log(this.values);
            // Record domains should always be over strings.
            return {
                "#type": "record",
                "#value": _.zipObject(this.domain.map(x => x.getVal()),
                    this.values.map(x => x.toJSONITF()))
            };
        } else {
            return {
                "#type": "map",
                "#value": _.zip(this.domain.map(x => x.toJSONITF()),
                    this.values.map(x => x.toJSONITF()))
            };
        }
    }
    fingerprint() {
        // Attempt normalization by sorting by fingerprints before hashing.
        let domFps = this.domain.map(v => v.fingerprint());
        let valsFp = this.values.map(v => v.fingerprint());

        let fcnPairs = _.zip(domFps, valsFp);
        let fcnPairsHashed = fcnPairs.map(hashSum);
        fcnPairsHashed.sort();
        return hashSum(fcnPairsHashed);
    }

    /**
     * Convert this function/record to a tuple, if it has a valid domain (i.e. {1,2,...,n}).
     */
    toTuple() {
        let dom = this.getDomain();
        // Domain must consist of all integral (i.e. natural numbered) values.
        if (!dom.every(v => v instanceof IntValue)) {
            throw "cannot convert record with domain '" + dom + "' to tuple";
        }
        let expectedDomain = _.range(1, dom.length + 1)
        let hasTupleDomain = _.isEqual(expectedDomain, _.sortBy(dom.map(v => v.getVal())));
        if (!hasTupleDomain) {
            throw "cannot convert record with domain '" + dom + "' to tuple";
        }
        let vals = this.getValues();
        let valsRevIndex = {};
        for (var ind = 0; ind < vals.length; ind++) {
            valsRevIndex[vals[ind]] = this.getDomain()[ind];
        }
        // Make sure the values are sorted by increasing indices.
        let sortedVals = _.sortBy(vals, v => valsRevIndex[v])
        return new TupleValue(sortedVals);
    }
}



// 
// TODO: Eventually consider moving over definition objects and table into these more structured formats.
// 

/**
 * Represents a TLA+ definition (either 0-arity or an n-arity operation definition.)
 */
// class Definition {
//     constructor(name, isLocalDef, infixOpSymbol, args, var_decls, op_defs, parentModuleName) {
//         this.name = name;
//         this.isLocalDef = isLocalDef;
//         this.infixOpSymbol = infixOpSymbol;
//         this.args = args;
//         this.var_decls = var_decls;
//         this.op_defs = op_defs;
//         this.parentModuleName = parentModuleName;
//     }
// }

/**
 * Stores a global table of definitions encountered during parsing a root spec and all imported/instantiated modules.
 */
// class GlobalDefinitionTable {
//     constructor() {
//         this.defs = {};
//     }

//     addDefinition(name, definition) {
//         this.defs[definition.parentModuleName + "$$$" + name] = definition;
//         definition.parentModuleName;
//         console.log("added definition", name, definition, definition.parentModuleName);
//     }
// }

/**
 * Represents a concrete TLA+ state i.e. a mapping from variable names to values.
 */
class TLAState {
    /**
     * Construct with a mapping from variable names to their corresponding TLAValue.
     */
    constructor(var_map) {
        this.stateVars = var_map;
    }

    hasVar(varname) {
        return this.stateVars.hasOwnProperty(varname);
    }

    static fromJSON(jsonval) {
        return new TLAState(_.mapValues(jsonval.stateVars, (v, k) => TLAValue.fromJSON(v)));
    }

    /**
     * Return the assigned value for the given variable name in this state.
     */
    getVarVal(varname) {
        return this.stateVars[varname];
    }

    /**
     * Return the state as an object mapping variables to values.
     */
    getStateObj() {
        return this.stateVars;
    }

    /**
     * Returns a new copy of this state with the given variable updated to the
     * specified value.
     */
    withVarVal(varName, newVal) {
        return new TLAState(_.mapValues(this.stateVars, (val, k, obj) => {
            if (k === varName) {
                return newVal;
            } else {
                return val;
            }
        }));
    }

    /**
     * Given a state with primed and unprimed variables, remove the original
     * unprimed variables and rename the primed variables to unprimed versions. 
     */
    deprimeVars() {
        let newVars = _.pickBy(this.stateVars, (val, k, obj) => k.endsWith("'"));
        return new TLAState(_.mapKeys(newVars, (val, k, obj) => k.slice(0, k.length - 1)));
    }

    /**
     * Return an object representing this state using the Informal Trace Format
     * (ITF) serialization conventions for TLA values.
     * 
     * See https://apalache.informal.systems/docs/adr/015adr-trace.html.
     */
    toJSONITF() {
        // Sort keys for now.
        let outObj = {};
        for (var k of Object.keys(this.stateVars).sort()) {
            outObj[k] = this.stateVars[k].toJSONITF();
        }
        return outObj;
        // return _.mapValues(this.vars, (v) => v.toJSONITF());
    }

    toString() {
        let out = "";
        for (var k of Object.keys(this.stateVars).sort()) {
            out += "/\\ " + k + " = " + this.stateVars[k].toString() + "\n";
        }
        return out;
    }

    /**
     * Return a unique, string hash of this state.
     */
    fingerprint() {
        let stateKeys = Object.keys(this.stateVars).sort();
        // Construct an array that is sequence of each state varialbe name and a
        // fingerprint of its TLA value. Then we hash this array to produce the
        // fingerprint for this state.
        let valsToHash = [];
        for (var k of stateKeys) {
            valsToHash.push(k);
            valsToHash.push(this.stateVars[k].fingerprint());
        }
        return hashSum(valsToHash);
    }

    // Compute the set of variables that are different between this state and the given 'otherState'.
    // Assumes they have the same set of state variables.
    varDiff(otherState){
        let stateKeys = Object.keys(this.stateVars).sort();
        // Construct an array that is sequence of each state varialbe name and a
        // fingerprint of its TLA value. Then we hash this array to produce the
        // fingerprint for this state.
        let varDiff = [];
        for (var k of stateKeys) {
            let mine = this.stateVars[k].fingerprint();
            let other = otherState.stateVars[k].fingerprint();
            if(mine !== other){
                varDiff.push(k);
            }
        }
        return varDiff;
    }

    // toString(){
    //     return "[" + this.domain.map((dv,idx) => dv + " |-> " + this.values[idx]).join(", ") + "]";
    // }

    // toJSON(){
    //     return _.fromPairs(_.zip(this.domain, this.values))
    // }    
}

/**
 * Represents an abstract action of a parsed specification (i.e. a sub-expression of the next state relation).
 */
class TLAAction{
    constructor(id, node, name) {
        this.id = id;
        this.node = node;
        this.name = name;
    }
}

/**
 * Generates and performs syntactic rewrites on a TLA+ spec as part of a
 * pre-processing step before parsing and evaluation.
 */
class SyntaxRewriter {

    setInUniqueVarId = 0;
    origSpecText;
    identUniqueId = 0;
    opArgsToRename = {};

    // Map from rewritten spec back to the original.
    // maps from (line_new, col_new) to (line_old, col_old)

    constructor(origSpecText, parser) {
        this.origSpecText = origSpecText;
        this.parser = parser;
        this.sourceMapOffsets = [];
    }

    /**
     * Generate and apply syntax rewrites on the original spec text repeatedly
     * until a fixpoint is reached i.e until no more rewrite operations can be
     * generated. Returns the rewritten version of the spec.
     */
    doRewrites() {
        // Start with the original spec text.
        this.sourceMapOffsets = [];
        let specTextRewritten = this.origSpecText;
        let specTree = this.parser.parse(specTextRewritten + "\n", null);

        // Generate initial rewrite batch.
        let rewriteBatch = this.genSyntaxRewrites(specTree);

        // Apply AST rewrite batches until a fixpoint is reached.
        const start = performance.now();
        while (rewriteBatch.length > 0) {
            // console.log("New syntax rewrite iteration");
            // console.log("rewrite batch: ", rewriteBatch, "length: ", rewriteBatch.length);
            specTextRewritten = this.applySyntaxRewrites(specTextRewritten, rewriteBatch);
            // console.log("REWRITTEN:", specTextRewritten);
            specTree = this.parser.parse(specTextRewritten + "\n", null);
            rewriteBatch = this.genSyntaxRewrites(specTree);
        }
        const duration = (performance.now() - start).toFixed(1);
        console.log(`Completed spec rewriting in ${duration}ms`)
        // console.log(specTextRewritten);
        return specTextRewritten;
    }

    /**
     * Compute original location of given position from the rewritten spec.
     */
    getOrigLocation(line, col) {
        return [line, col];
        console.log("#getOrigLocation");
        let lineArg = line;
        let colArg = col;
        console.log("initial curr line,col:", lineArg, colArg);
        for (var f of _.reverse(this.sourceMapOffsets)) {
            // for (var f of this.sourceMapOffsets) {
            // console.log("smap:", f);

            let newPos = f(lineArg, colArg);
            lineArg = newPos[0];
            colArg = newPos[1];

            // let posAfter = m[0];
            // let lineAfter = posAfter[0]
            // let colAfter = posAfter[1];
            // // Inverse the diff direction as we apply the offsets.
            // let lineDiff = -m[1];
            // let colDiff = -m[2];

            // // Is the given position after the start of the rewritten portion?
            // // Otherwise no offset is required.
            // if (lineArg === lineAfter && colArg >= colAfter) {
            //     // lineArg unchanged.
            //     colArg += colDiff
            // }
            // else if (lineArg > lineAfter) {

            //     console.log("diff:", lineAfter, colDiff);
            //     if (lineArg > lineAfter) {
            //         lineArg += lineDiff;
            //         if (lineArg == lineAfter) {
            //             colArg += colDiff;
            //         }
            //     }
            // }
            // console.log("curr line,col:", lineArg, colArg);
        }
        return [lineArg, colArg];
    }

    // Apply a given set of text rewrites to a given source text. Assumes the given
    // 'text' argument is a string given as a list of lines.
    applySyntaxRewrites(text, rewrites) {
        // console.log("num rewrites:", rewrites.length);

        // Sort rewrites from bottom to top, with later rows coming first. This
        // allows us to apply batches of rewrites without worrying about earlier
        // rewrites in the document affecting positions of later ones. 
        rewrites.sort((a, b) => {
            let aRow = a["startPosition"]["row"];
            let bRow = b["startPosition"]["row"];
            if (aRow === bRow) {
                // If same row, sort by column descending
                return b["startPosition"]["column"] - a["startPosition"]["column"];
            }
            // Sort by row descending
            return bRow - aRow;
        });

        let lines = text.split("\n");
        // let sourceMapFn = (line, col) => (line, col);

        for (const rewrite of rewrites) {
            let startRow = rewrite["startPosition"]["row"];
            let startCol = rewrite["startPosition"]["column"];
            let endRow = rewrite["endPosition"]["row"];
            let endCol = rewrite["endPosition"]["column"];

            // Cut out original chunk.
            let prechunk = lines.slice(0, startRow).concat([lines[startRow].substring(0, startCol)]);
            let postchunk = [lines[endRow].substring(endCol)].concat(lines.slice(endRow + 1));

            // console.log("chunk out: ");
            // console.log(prechunk.join("\n").concat("<CHUNK>").concat(postchunk.join("\n")));
            // console.log("postchunk: ");
            // console.log(postchunk.join("\n"));

            // Delete line entirely.
            if (rewrite["deleteRow"] !== undefined) {
                lines[rewrite["deleteRow"]] = "";
                // TODO: Make this work.
                // lines = lines.filter((_, index) => index !== rewrite["deleteRow"]);
            } else {
                let lineInd = rewrite["startPosition"]["row"]
                let line = lines[lineInd];

                // < 
                //   PRECHUNK
                //    >|< 
                //  CHUNK TO REPLACE
                //    >|<
                //   POST CHUNK
                // >

                // Append the new string to the last line of the prechunk,
                // followed by the first line of the post chunk.
                prechunk[prechunk.length - 1] = prechunk[prechunk.length - 1].concat(rewrite["newStr"]).concat(postchunk[0]);
                // Then append the rest of the postchunk
                let linesUpdated = prechunk.concat(postchunk.slice(1));

                //
                // TODO: Revisit how to do source mapping here for error reporting.
                //

                // Everything after the changed lines must be shifted but everything before 
                // remain reamin the same.
                // let afterPos = [startRow, startCol];
                // let lineDiff = -(endRow - startRow)
                let colDiff = (rewrite["newStr"].length - prechunk.length);
                // let diff = [afterPos, lineDiff, colDiff];
                // this.sourceMapOffsets.push(diff);

                let newStartRow = startRow;
                let newStartCol = startCol;

                //////////////////////
                // TODO!! Goal is to just try to get rid of rewrites entirely
                // and just fix the few remaining cases where the interpreter
                // was relying on rewrites for semantic correctness!
                //////////////////////

                // Assume all new rewritten blocks are one-liners, so the the new end row will always be the same as the
                // start row of the chunk being rewritten.
                let newEndRow = startRow;
                let newEndCol = prechunk[prechunk.length - 1].length + rewrite["newStr"].length - 1;

                let transform = (targetRow, targetCol) => {
                    // console.log("newStartRow, newEndRow", newStartRow, newEndRow);
                    // console.log("start", newEndRow);
                    // if(targetRow < newStartRow){
                    //     return [targetRow, targetCol];
                    // }

                    // Target position is >= the new chunk end position.
                    if (targetRow > startRow || targetRow === newEndRow && targetCol >= newEndCol) {
                        // Shift by line diff, and by column diff (if necessary).
                        // Diff from end of new chunk.
                        let lineDiff = targetRow - newEndRow;
                        let colDiff = targetRow === newEndRow ? targetCol - newEndCol : newEndCol;
                        // console.log("lineDiff:", lineDiff);
                        // console.log("colDiff:", colDiff);
                        // console.log("startRow:", startRow);
                        // console.log("startRow:", startRow);

                        // Transformed position is equivalent to same diff from original end position.
                        return [endRow + lineDiff, endCol + colDiff]
                    } else {
                        // No shift.
                        return [targetRow, targetCol];
                    }

                    // if(targetRow === newStartRow && targetCol == newStartCol){
                    //     return [startRow, startCol]
                    // }

                    // if(targetRow === startRow && targetCol == newEndCol){
                    //     return [endRow, endCol]
                    // }
                    // if(targetRow > startRow){
                    //     let lineDiff = endRow - startRow;
                    //     if(targetRow === end)
                    //     return [targetRow + lineDiff, endCol]
                    // }
                    // return [targetRow, targetCol];
                }

                this.sourceMapOffsets.push(transform);


                lines = linesUpdated;
            }

            // TODO: Consider removing line entirely if it is empty after rewrite.
            // if(lineNew.length > 0){
            // lines[lineInd] = lineNew;
            // } else{
            // If line is empty, remove it.
            // lines.splice(lineInd, 1);
            // }
        }
        return lines.join("\n");
    }

    /**
     * Walks a given TLA syntax tree and generates a new batch of syntactic rewrites to be
     * performed on the source module text before we do any evaluation/interpreting
     * e.g. syntactic desugaring. Should be repeatedly applied until no more rewrites are
     * produced.
     * 
     * @param {TLASyntaxTree} treeArg 
     */
    genSyntaxRewrites(treeArg) {
        // Records a set of transformations to make to the text that produced this
        // parsed syntax tree. Each rewrite is specified by a replacement rule,
        // given by a structure {startPosition: Pos, endPosition: Pos, newStr: Str}
        // where startPosition/endPosition correspond to the start and end points of
        // the source text to replace, and 'newStr' represents the string to insert
        // at this position.
        let sourceRewrites = [];

        const cursor = treeArg.walk();
        // isRendering = false;

        let currentRenderCount = 0;
        let row = '';
        let rows = [];
        let finishedRow = false;
        let visitedChildren = false;
        let indentLevel = 0;

        let currOpDefNameContext = null;

        for (let i = 0; ; i++) {
            let displayName;
            if (cursor.nodeIsMissing) {
                displayName = `MISSING ${cursor.nodeType}`
            } else if (cursor.nodeIsNamed) {
                displayName = cursor.nodeType;
            }

            if (visitedChildren) {
                if (displayName) {
                    finishedRow = true;
                }

                if (cursor.gotoNextSibling()) {
                    visitedChildren = false;
                } else if (cursor.gotoParent()) {
                    visitedChildren = true;
                    indentLevel--;
                } else {
                    break;
                }
            } else {
                if (displayName) {
                    if (finishedRow) {
                        finishedRow = false;
                    }
                    const start = cursor.startPosition;
                    const end = cursor.endPosition;
                    const id = cursor.nodeId;
                    let fieldName = cursor.currentFieldName();
                    //   console.log(fieldName);
                    if (fieldName) {
                        fieldName += ': ';
                    } else {
                        fieldName = '';
                    }
                    let node = cursor.currentNode();

                    // console.log("(REWRITE) NODE:", node.text);
                    // console.log("(REWRITE) NODEtype:", node.type);
                    // console.log("Opargstorename:", this.opArgsToRename);

                    // Detect errors.
                    if (node.type === "ERROR") {
                        throw new Error("Parsing error.", { cause: node });
                    }

                    // Delete everything inside comments.
                    if (node.type === "block_comment") {
                        // sourceRewrites.push({
                        //     startPosition: node.startPosition,
                        //     endPosition: node.endPosition,
                        //     newStr: ""
                        // });
                        // return sourceRewrites;
                    }

                    // Comments.
                    if (node.type === "comment") {
                        let rewrite = {
                            startPosition: node.startPosition,
                            endPosition: node.endPosition,
                            newStr: "",
                            // TODO: Delete line.
                            // deleteRow: node.startPosition["row"]
                        }
                        // sourceRewrites.push(rewrite);
                        // return sourceRewrites;
                    }

                    // Bound infix ops.
                    if (node.type === "bound_infix_op") {
                        let symbol = node.childForFieldName("symbol");
                        let rhs = node.childForFieldName("rhs");
                        // console.log("syntax rewriting:", symbol);
                        // console.log("syntax rewriting, type:", symbol.type);

                        // x \in S, x \notin S
                        if (symbol.type === "in" || symbol.type === "notin") {
                            // Rewrite '<expr> \in S' as '\E h \in S : <expr> = h'
                            // console.log("REWRITE SETIN", node);

                            let expr = node.namedChildren[0];
                            let domain = node.namedChildren[2];

                            // console.log("REWRITE SETIN expr", expr.text);
                            // console.log("REWRITE SETIN domain", domain.text);

                            // Generate a unique identifier for this new quantified variable.
                            // The hope is that it is relatively unlikely to collide with any variables in the spec.
                            // TODO: Consider how to ensure no collision here in a more principled manner.
                            let newUniqueVarId = "SETINREWRITE" + this.setInUniqueVarId;
                            this.setInUniqueVarId += 1;
                            let neg = symbol.type === "notin" ? "~" : "";
                            let outStr = `(${neg}(\\E ${newUniqueVarId} \\in ${domain.text} : ${expr.text} = ${newUniqueVarId}))`
                            let rewrite = {
                                startPosition: node.startPosition,
                                endPosition: node.endPosition,
                                newStr: outStr
                            }
                            // REWRITE DISABLED.
                            // sourceRewrites.push(rewrite);
                            // return sourceRewrites;
                        }

                    }
                    
                    // TODO: Initial framework for rewriting operator arguments to enforce global argname uniqueness.
                    // But, need to think a bit more carefully about how this works in all cases e.g. with LAMBDA expressions
                    // and nested LET-IN operator definitions, before we enable this via above syntax rewrite generation logic.
                    
                    /**
                    if(node.type === "operator_definition"){
                        continue;

                        let opName = node.namedChildren[0].text;
                        let opArgsIdents = node.namedChildren.slice(1).filter(n => n.type === "identifier");
                        let opArgsDecls = node.namedChildren.slice(1).filter(n => n.type === "operator_declaration");

                        // Update the current context.
                        currOpDefNameContext = opName;

                        let opArgsIdentsNames = opArgsIdents.map(n => n.text).filter(n => !n.includes("IDENTRENAMED"));
                        let opArgsDeclNames = opArgsDecls.map(n => n.namedChildren[0].text).filter(n => !n.includes("IDENTRENAMED"));
                        // console.log("PARSE opArg:", opName);
                        // console.log("PARSE idents:", opArgsIdents);
                        // console.log("PARSE idents:", opArgsIdentsNames);
                        // console.log("PARSE decls:", opArgsDecls);
                        // console.log("PARSE decls:", opArgsDeclNames);

                        // Do a uniqifer rename pass of all references to these operator args in the direct body of this operator.
                        let opBodyNode = _.last(node.namedChildren);
                        // console.log("PARSE BODY:", opBodyNode.text);
                        let argsToRename = opArgsIdentsNames.concat(opArgsDeclNames);

                        if(!this.opArgsToRename.hasOwnProperty(opName)){
                            this.opArgsToRename[opName] = {"argsToRenameMap": {}};
                        }
                        this.identUniqueId += 1;
                        let argsToRenameMap = {}
                        for(const a of argsToRename){
                            argsToRenameMap[a] = a + "_IDENTRENAMED_" + this.identUniqueId;
                            this.opArgsToRename[opName]["argsToRenameMap"][a] = argsToRenameMap[a];
                        }
                    }
                    **/

                    if (node.type == "bounded_quantification") {
                        //
                        // In general, bounded quantifiers can look like:
                        // \E i,j \in {1,2,3}, x,y,z \in {4,5,6}, u,v \in {4,5} : <expr>
                        //
                        // Rewrite all quantifiers to a normalized form i.e.
                        // \E i1 \in S1 : \E i2 \in S2 : ... : \E in \in Sn : <expr>
                        //

                        // TODO: Make sure this works for quantifier expressions that span multiple lines.

                        let quantifier = node.childForFieldName("quantifier");
                        let quantifierBoundNodes = node.namedChildren.filter(c => c.type === "quantifier_bound");//  slice(1,node.namedChildren.length-1);
                        // let exprNode = node.childForFieldName("expression");

                        // Don't re-write if already in normalized form.
                        let isNormalized = quantifierBoundNodes.length === 1 && (quantifierBoundNodes[0].namedChildren.length === 3);
                        // console.log(node);
                        // console.log("bound nodes:", quantifierBoundNodes);
                        // console.log("REWRITE quant is normalized: ", isNormalized);

                        if (!isNormalized) {
                            // console.log("REWRITE quant:", node);
                            // console.log("REWRITE quant bound nodes:", quantifierBoundNodes);

                            // Expand each quantifier bound.
                            let quantBounds = quantifierBoundNodes.map(boundNode => {
                                let quantVars = boundNode.namedChildren.filter(c => c.type === "identifier");
                                let quantBound = boundNode.namedChildren[boundNode.namedChildren.length - 1];
                                // For \E and \A, rewrite:
                                // <Q> i,j \in S ==> <Q> i \in S : <Q> j \in S
                                // console.log(quantVars.map(c => c.text));
                                // console.log(quantVars);
                                // console.log("quantifier:",quantifier);
                                return quantVars.map(qv => [quantifier.text, qv.text, "\\in", quantBound.text].join(" ")).join(" : ");
                            })

                            let outStr = quantBounds.join(" : ");
                            // console.log("rewritten:", outStr);
                            let rewrite = {
                                startPosition: quantifier.startPosition,
                                endPosition: quantifierBoundNodes[quantifierBoundNodes.length - 1].endPosition,
                                newStr: outStr
                            }
                            // REWRITE DISABLED.
                            // sourceRewrites.push(rewrite);
                            // return sourceRewrites;
                        }

                    }

                    finishedRow = true;
                }

                if (cursor.gotoFirstChild()) {
                    visitedChildren = false;
                    indentLevel++;
                } else {
                    visitedChildren = true;
                }
            }
        }
        if (finishedRow) {
            row += '</div>';
            rows.push(row);
        }

        cursor.delete();
        return sourceRewrites
    }
}

function checkModelValSet(exprNode){
    if(exprNode.type === "finite_set_literal"){
        console.log(exprNode.namedChildren);
        let all_idents = exprNode.namedChildren.every(n => n.type === "identifier_ref");
        // Treat these all as model values, identified their identifier ref string name.
        if(all_idents){
            console.log("Ident set")
            let identSet = exprNode.namedChildren.map(n => n.text);
            identSet = _.uniq(identSet);
            let modelValueSet = new SetValue(identSet.map(n => new ModelValue(n)));
            return modelValueSet;
        }
        // otherwise, try to evaluate.
    }
    return null;    
}

/**
 * Evaluate a TLA+ expression, given as a string, in the given context.
 */
function evalExprStrInContext(evalCtx, exprStr, exprTagName = "temp") {
    let nullTree;
    let start = performance.now();

    // Create a dummy spec to parse/evaluate the expression.
    let dummySpec = `---- MODULE expr_eval_spec_${exprTagName} ----\n`;
    dummySpec += `Expr == ${exprStr}\n`;
    dummySpec += "====";

    let spec = new TLASpec(dummySpec);
    spec.parseSync();
    let dummyTreeObjs = spec.spec_obj;

    let opDefs = dummyTreeObjs["op_defs"];
    let exprNode = spec.getDefinitionByName("Expr").node

    let exprVal = evalExpr(exprNode, evalCtx)[0]["val"];

    const duration = (performance.now() - start).toFixed(1);
    // console.log("return val:", exprVal);
    // console.log("compute duration val ms:", duration);
    return exprVal;
}

// Parse a TLA+ expression string into a syntax node that can replace a definition body.
// This does not evaluate the expression; it only returns the AST node for the expression.
function parseExprToNode(exprStr) {
    let dummySpec = `---- MODULE expr_eval_spec_tmp ----\n`;
    dummySpec += `Expr == ${exprStr}\n`;
    dummySpec += "====";

    let spec = new TLASpec(dummySpec);
    spec.parseSync();
    let exprNode = spec.getDefinitionByName("Expr").node;
    return exprNode;
}

/**
 * Return action name for a given action node.
 */
function extractActionName(node) {
    // TODO: Check these cases to determine all action name extraction scenarios.
    if(node.type === "identifier_ref"){
        return node.text;
    }
    if (node.type === "bound_op") {
        let opName = node.namedChildren[0].text;
        return opName;
    }
    if (node.type === "bounded_quantification") {
        // Strip away all outer quantifiers.
        let curr_node = node;
        while (curr_node.type === "bounded_quantification") {
            curr_node = curr_node.namedChildren.at(-1);
        }
        return curr_node.text;
    } else {
        return node.text;
    }
}

// TODO: Extend this to parse fetched modules during spec parsing.
function fetchModuleExtends(moduleNames, urlPath) {
    console.log("Fetching module extends");
    console.log(decodeURIComponent(urlPath));
    const segments = decodeURIComponent(urlPath).split("/");
    const baseSpecPath = segments.slice(0, segments.length - 1).join("/");
    $.get(`${baseSpecPath}/${moduleNames[1]}.tla`, function (data) {
        console.log("Fetched module spec");
        console.log(data)
    });
}

/**
 * Represents a parsed TLA+ specification, with helper methods and structures for 
 * maintaining module extends/instances from a root module, etc.
 */
class TLASpec {
    // TODO: We probably want to eventually rename this to more accurately represent its role as a single (e.g. root) TLA+ module.
    constructor(specText, specPath, nextDefName="Next", module_overrides={}) {

        this.moduleTable = {};
        this.moduleTableParsed = {};

        // Stores global table of all definitions encountered during parsing of any module.
        this.globalDefTable = {};
        this.globalDefId = 0;

        this.specText = specText;
        this.specPath = specPath;

        // Stores the parsed root spec object.
        this.spec_obj = {};

        // An optional map that can be supplied that maps from a module name to
        // the full text of that module to use if any module during parsing is
        // looked up by that name.
        this.module_overrides = module_overrides;

    }

    /**
     * Generate a globally unique identifier for a definition. 
     * 
     * We use numerical identifiers but these can be considered as string
     * identifiers.
     */
    nextGlobalDefId() {
        let nextId = this.globalDefId;
        this.globalDefId += 1;
        return String(nextId);
    }

    hasDefinitionByName(defName){
        return this.getDefinitionByName(defName) !== undefined;
    }

    getDefinitionByName(defName){
        let defObj = _.find(this.spec_obj["op_defs"], (defobj) => defobj.name === defName);
        return defObj;
    }

    // TODO: Extend this to parse fetched modules during spec parsing.
    fetchModules(moduleNames, urlPath) {
        console.log("Fetching modules", moduleNames, "for spec at root path:", urlPath);
        // console.log("module names:", moduleNames);
        // console.log(decodeURIComponent(urlPath));
        const segments = decodeURIComponent(urlPath).split("/");
        const baseSpecPath = segments.slice(0, segments.length - 1).join("/");

        // Fetch all module names, ignoring TLA+ standard modules.
        let modulesToFetch = moduleNames.filter(m => !TLA_STANDARD_MODULES.includes(m));

        // console.log("fetching modules:", modulesToFetch);
        let modulePromises = modulesToFetch.map(function (modName) {

            // Look up CommunityModule imports from hard-coded repo.
            // TODO: This will likely not work properly unitl we handle LOCAL INSTANCE 
            // semantics correctly for modules.
            if (TLA_COMMUNITY_MODULES.includes(modName)) {
                return fetch(`${TLA_COMMUNITY_MODULES_BASE_URL}/${modName}.tla`).then(response => response.text());
            }

            return fetch(`${baseSpecPath}/${modName}.tla`).then(response => response.text());
        });

        var self = this;
        return Promise.all(modulePromises).then(moduleTextValues => {
            return _.zipObject(modulesToFetch, moduleTextValues);
        });
    }

    /**
     * Parse a module given as text and extract set of module names that are
     * imported/extended in this module. 
     *
     * Does not do any further fetching/parsing on the set of imported modules.
     */
    extractModuleImports(specText) {

        // Perform syntactic rewrites.
        // 
        // N.B. I don't think we need to do spec re-writing before fetching module table graph?
        // 
        // let rewriter = new SyntaxRewriter(specText, parser);
        // let specTextRewritten = rewriter.doRewrites();
        // specText = specTextRewritten;

        // Now parse the rewritten spec to extract definitions, variables, etc.
        let tree = parser.parse(specText + "\n", null);
        let cursor = tree.walk();

        // One level down from the top level tree node should contain the overall TLA module.
        cursor.gotoFirstChild();
        let node = cursor.currentNode();
        assert(node.type === "module" || node.type === "extramodular_text");

        // Extramodular text is considered as comments, to be ignored.
        if (node.type === "extramodular_text") {
            console.log("ignoring extramodular_text");
            cursor.gotoNextSibling();
            node = cursor.currentNode();
            assert(node.type === "module");
        }

        let imported_modules = [];

        // Look for all variables and definitions defined in the module.
        let more = cursor.gotoFirstChild();
        while (more) {
            more = cursor.gotoNextSibling();
            let node = cursor.currentNode();
            // console.log(node);
            // console.log("node type:", node.type);
            // console.log("node text:", node.text);
            // console.log("node id:", node.id);

            // EXTENDS M
            if (node.type === "extends") {
                let extendsList = cursor.currentNode().namedChildren;
                let extendsModuleNames = extendsList.map(n => n.text);
                imported_modules = imported_modules.concat(extendsModuleNames);
            }

            // INSTANCE M [WITH A <- 5, B <- 6]
            if (node.type === "instance") {
                let instanceModName = cursor.currentNode().namedChildren[0].text;
                imported_modules.push(instanceModName);
            }

            // Module instantiation like:
            // M1 == INSTANCE Module1 WITH A <- 5, ...
            // M1(x,y) == INSTANCE Module1 WITH A <- 5, ...
            if (node.type === "module_definition") {
                let nodes = cursor.currentNode().namedChildren;
                let params = cursor.currentNode().namedChildren.filter(n => n.type === "identifier").slice(1);
                console.log(nodes)
                console.log(params);

                // Extract the name of the module being instantiated.
                // e.g. INSTANCE Module1 WITH A <- 5
                let instance = cursor.currentNode().namedChildren.filter(n => n.type === "instance")[0];
                let modName = instance.namedChildren[0].text;

                imported_modules = imported_modules.concat(modName);
            }

        }

        return imported_modules;
    }

    /**
     * Given text of a root TLA+ module, discovers all transitive module dependencies
     * required by this root module, and builds a table mapping from module name
     * to full module text for every module in this set. 
     * 
     * Does not explicitly maintain module dependency graph or imported
     * definitions/declarations. We assume that is done after using the table
     * built and returned by this function.
     */
    resolveModuleImports(rootModuleText) {
        var self = this;

        let importedModules = this.extractModuleImports(rootModuleText);
        console.log("imported modules:", importedModules);

        // For each imported module, we fetch its text. This gives us a map from
        // module names to their full module text.
        return this.fetchModules(importedModules, this.specPath).then(function (importedModuleMap) {
            // A map from module name to full module text.
            // console.log("MAP:", importedModuleMap);
            // For each module, we now parse it again to extract module imports, and recurse to fetch its imported modules.
            let allPromises = [];
            for (const modName in importedModuleMap) {
                // Recursively resolve module imports for each fetched module.
                let ret = self.resolveModuleImports(importedModuleMap[modName]);
                allPromises.push(ret);
            }

            return Promise.all(allPromises).then(function (vals) {
                // Merge all discovered module tables together.
                for (const v of vals) {
                    importedModuleMap = _.merge(importedModuleMap, v);
                }
                return importedModuleMap;
            })
        })
    }

    /**
     * 
     * Parse a TLA+ spec viewed as the raw, root module text and its path.
     */
    async parse() {
        // First resolve any module imports, and then parse the spec
        // and any modules in the module import hierarchy.
        console.log("Parsing spec from path:", this.specPath);
        var self = this;

        return this.resolveModuleImports(this.specText).then(function (fullModuleTable) {
            console.log(`Resolved module table (${Object.keys(fullModuleTable).length} transitively imported modules):`, Object.keys(fullModuleTable));
            // console.log("FULL MODULE TABLE:", fullModuleTable);
            self.moduleTable = fullModuleTable;

            // If there explicit module overrides, we set those in the constructed module table.
            if(self.module_overrides){
                for(const modName in self.module_overrides){
                    self.moduleTable[modName] = self.module_overrides[modName];
                }
            }

            // 
            // Once the global module table has been fetched and stored, we shouldn't need to fetch any more specs.
            // Now, we just go through and parse the text of each fetched module and store it.
            // 
            // console.log("Pre-parsing all modules in global module table.");
            // for (const modName in fullModuleTable) {
            //     let parsedObj = self.parseSpecModule(fullModuleTable[modName]);
            //     self.moduleTableParsed[modName] = parsedObj;
            // }

            // Now parse the root module, which will use the global module table as needed as it proceeds.
            console.log("PARSING ROOT MODULE:", self.specPath);
            let parsedSpec = self.parseSpecModule(self.specText);
            self.spec_obj = parsedSpec;
            self.spec_obj["module_table"] = self.moduleTableParsed;

            // TODO. Walk through the module import graph to determine the set of
            // definitions/declarations that should be defined via import in the root module.

            console.log("PARSED MODULE TABLE:", self.moduleTableParsed);
            console.log("GLOBAL DEF TABLE:", self.globalDefTable);
            return parsedSpec;
        });
    }

    /**
     * A synchronous version of 'parse' that can be used only if it is guaranteed that the given
     * specification has no imported/instantiated modules.
     * @returns 
     */
    parseSync() {
        // First resolve any module imports, and then parse the spec
        // and any modules in the module import hierarchy.
        this.moduleTable = {};
        let parsedSpec = this.parseSpecModule(this.specText);
        this.spec_obj = parsedSpec;
        this.spec_obj["module_table"] = {};
        return parsedSpec;
    }


    /**
     * Extract set of actions from a syntax node.
     */
    parseActionsFromNode(node, ind){
        let actions = this.parseActionsFromNodeRec(node, ind);
        if(actions.includes(null)){
            actions = [new TLAAction(0, node, "Next")];
        }
        for(var i = 0; i < actions.length; i++){
            actions[i].id = i;
        }
        return actions;
    }

    parseActionsFromNodeRec(node, ind){
        if(ind === undefined){
            ind = 0;
        }

        // Clear comments eagerly.
        _.remove(node.children, isCommentNode);
        _.remove(node.namedChildren, isCommentNode);

        // De-parenthesize.
        if(node.type === "parentheses"){
            return this.parseActionsFromNodeRec(node.namedChildren[0], ind);
        }

        // If an action is just a plain identifier, then we treat it as its own action.
        if (node.type === "identifier_ref") {
            return [new TLAAction(ind, node, extractActionName(node))];
        }

        // Parameterized action like \E s \in Server : Action(s).
        if (node.type === "bounded_quantification") {
            return [new TLAAction(ind, node, extractActionName(node))];
        }

        if(node.type === "bound_infix_op"){
            let lhs = node.children[0];
            let symbol = node.children[1];
            let rhs = node.children[2];
            evalLog("infix:", lhs, symbol, rhs);
            
            // Disjunction A \/ B.
            if(symbol.type === "lor"){
                return this.parseActionsFromNodeRec(lhs).concat(this.parseActionsFromNodeRec(rhs));
            }
        }

        // For a disjunction list, recurse on each disjunct.
        if (node.type == "disj_list") {
            let disjActions = node.namedChildren.map((cnode, ind) => {
                return this.parseActionsFromNodeRec(cnode.namedChildren[1], ind);
            });
            return _.flatten(disjActions);
        }

        return [new TLAAction(ind, node, extractActionName(node))]; // TODO: fix.
    }

    /**
     * Parse and extract definitions and declarations from the given TLA+ module text.
     */
    parseSpecModule(specText) {
        var self = this;

        // Perform syntactic rewrites.
        let rewriter = new SyntaxRewriter(specText, parser);
        this.rewriter = rewriter;
        // Fully disable syntactic re-writing.
        // let specTextRewritten = rewriter.doRewrites();
        let specTextRewritten = specText;
        this.specTextRewritten = specText;
        specText = specTextRewritten;

        // console.log("REWRITTEN:");
        // console.log(specText);

        // let orig = rewriter.getOrigLocation(7, 14);
        // console.log("ORIGLOC:", orig);

        // Now parse the rewritten spec to extract definitions, variables, etc.
        let tree = parser.parse(specText + "\n", null);
        let cursor = tree.walk();

        // One level down from the top level tree node should contain the overall TLA module.
        cursor.gotoFirstChild();
        let node = cursor.currentNode();
        assert(node.type === "module" || node.type === "extramodular_text");

        // Extramodular text is considered as comments, to be ignored.
        if (node.type === "extramodular_text") {
            console.log("ignoring extramodular_text");
            cursor.gotoNextSibling();
            node = cursor.currentNode();
            assert(node.type === "module");
        }

        let root_mod_name = node.namedChildren[1].text;
        let op_defs = {};
        let imported_op_defs = {};
        let var_decls = {};
        let const_decls = {};
        let extends_modules = [];
        let instance_modules = {};

        // console.log(`>>> Processing MODULE after extracting definitions: '${root_mod_name}'`);

        // Look for all variables and definitions defined in the module.
        let more = cursor.gotoFirstChild();
        while (more) {
            more = cursor.gotoNextSibling();
            let node = cursor.currentNode();
            // console.log(node);
            // console.log("node type:", node.type);
            // console.log("node text:", node.text);
            // console.log("node id:", node.id);

            // EXTENDS M1, M2, M3
            if (node.type === "extends") {
                let extendsList = cursor.currentNode().namedChildren;
                let extendsModuleNames = extendsList
                    .map(n => n.text)
                    .filter(m => !TLA_STANDARD_MODULES.includes(m));


                // For each module we extend, we should parse it and store it in 
                // the global module lookup table.
                extendsModuleNames.map(function (modName) {
                    console.log("EXTENDS module:", modName);
                    let parsedObj = self.parseSpecModule(self.moduleTable[modName]);
                    if (!self.moduleTableParsed.hasOwnProperty(modName)) {
                        self.moduleTableParsed[modName] = parsedObj;
                    }

                    // Go ahead and add all definitions from this module to the current module (?)
                    // TODO: Should not include LOCAL
                    console.log("current op_defs:", _.clone(op_defs));
                    console.log("parsedObj:", parsedObj["op_defs"]);
                    op_defs = _.merge(op_defs, _.pickBy(parsedObj["op_defs"], (d) => {
                        if(!d.hasOwnProperty("is_local")){
                            return true;
                        }
                        return !d.is_local;
                    }));

                    // Also import any declarations (variables or constants) from the module into
                    // the current one.
                    var_decls = _.merge(var_decls, parsedObj["var_decls"]);
                    const_decls = _.merge(const_decls, parsedObj["const_decls"]);

                    // Save the imported definitions globally.
                    self.globalDefTable = _.merge(self.globalDefTable, parsedObj["op_defs"]);
                })

                extends_modules = extendsModuleNames;
                console.log("  All EXTENDS modules:", extends_modules);
            }

            //
            // INSTANCE N INSTANCE M WITH A <- 5, B <- 6
            //
            // An INSTANCE N statement inside a module M dumps all definitions
            // from module N into module M. Note that it does not include any
            // VARIABLE or CONSTANT declarations from N into M. This also means,
            // though, that substitutions may be required in the INSTANCE
            // statement for either VARIABLE or CONSTANT symbol declarations
            // that appear in N but not in M.
            //
            if (node.type === "instance") {
                let instanceNodes = cursor.currentNode().namedChildren;
                let modName = instanceNodes[0].text;
                let substs = instanceNodes.filter(n => n.type === "substitution");
                console.log("INSTANCE modname:", instanceNodes);
                console.log("INSTANCE LIST:", modName);
                console.log("INSTANCE subs:", substs);

                console.log("Parsing INSTANCE module:", modName);
                let parsedObj = self.parseSpecModule(self.moduleTable[modName]);
                if (!self.moduleTableParsed.hasOwnProperty(modName)) {
                    self.moduleTableParsed[modName] = parsedObj;
                }

                //
                // Go ahead and add all definitions from this module to the
                // current module.
                //
                // Definitions imported via module instantiation are treated a
                // bit specially to account for substitutions. Alongside the
                // definition, we to store the substitutions that go with it so
                // that it can be evaluated correctly.
                // 
                for (const opName in parsedObj["op_defs"]) {
                    let defId = self.nextGlobalDefId();

                    let origOpDef = parsedObj["op_defs"][opName];

                    let substPairs = substs.map(s => [s.namedChildren[0].text, {"node":s.namedChildren[2], "curr_defs_context": _.keys(op_defs)}]);
                    let currentSubs = parsedObj["op_defs"][opName]["substitutions"];

                    // Add any new substitutions to already existing set of substitutions for this definition.
                    parsedObj["op_defs"][opName]["substitutions"] = _.merge(currentSubs, _.fromPairs(substPairs));

                    let newSubs = _.merge(currentSubs, _.fromPairs(substPairs));

                    op_defs[defId] = { 
                        "id": defId,
                        "name": origOpDef.name, 
                        "args": origOpDef.args, 
                        "node": origOpDef.node, 
                        "name_prefix": "", 
                        "parent_module_name": root_mod_name,
                        "module_name": modName,
                        "substitutions": newSubs,
                        "module_defs": parsedObj["op_defs"],
                        "module_param_args": null,
                        "curr_defs_context": origOpDef["curr_defs_context"]
                    };
                    self.globalDefTable[defId] = op_defs[defId];
                }
            }

            //
            // Foo == INSTANCE Bar WITH A <- 5, B <- 6, ...
            //
            if (node.type === "module_definition") {
                let nodes = cursor.currentNode().namedChildren;

                // Get the 'Foo' from 'Foo == INSTANCE Bar...'.
                let moduleDefName = nodes[0].text;

                //
                // Arguments for parameterized module instantiation definition, if they exist.
                // 
                // e.g. M(x,y) == INSTANCE Module1 WITH A <- x + y
                // 
                let paramModArgs = cursor.currentNode().namedChildren.filter(n => n.type === "identifier").slice(1);
                let numModuleParams = paramModArgs.length
                if (numModuleParams > 0) {
                    evalLog("module_def params:", paramModArgs.map(n => n.text))
                }

                // Extract the name of the module being instantiated.
                // e.g. INSTANCE Module1 WITH A <- 5
                let instance = cursor.currentNode().namedChildren.filter(n => n.type === "instance")[0];
                let modName = instance.namedChildren[0].text;

                // Add substituted definitions into current module.
                evalLog(`Parsing module '${modName}' from namespaced INSTANCE definition: ${moduleDefName} == INSTANCE ${modName}`);

                // Extract substitutions from the module instantiation statement.
                // console.log(instance);
                // console.log(nodes);
                let substs = instance.namedChildren.filter(n => n.type === "substitution");
                evalLog(`Found ${substs.length} substitutions for module instantiation.`, substs.map(s => s.text));

                let parsedObj = self.parseSpecModule(self.moduleTable[modName]);
                // For any declarations that appear in the instantiated module
                // witout explicit substitutions, we fill them in implicitly
                // with the identity substitution.
                let allNonSubDecls = _.union(_.keys(parsedObj.var_decls), _.keys(parsedObj.const_decls)).filter(d => !substs.some(s => s.namedChildren[0].text === d));

                // For all the implicitly defined substitutions, there must be an actual identifier
                // that was already defined in scope for these.
                let allCurrDefsAndDecls = _.keys(op_defs).map(k => op_defs[k].name).concat(_.keys(const_decls),_.keys(var_decls));

                // console.log("allCurrDefsAndDecls:", allCurrDefsAndDecls);
                // console.log("allNonSubDecls:", allNonSubDecls);
                // console.log("modName:", modName);

                for(const d of allNonSubDecls){
                    assert(allCurrDefsAndDecls.includes(d), `Substitution '${d}' is not defined in the current scope of module '${modName}'`);
                }

                if (!self.moduleTableParsed.hasOwnProperty(modName)) {
                    self.moduleTableParsed[modName] = parsedObj;
                }
                

                // Definitions imported via module instantiation are treated a
                // bit specially to account for substitutions. Alongside the
                // definition, we to store the substitutions that go with it so
                // that it can be evaluated correctly.
                // 
                for (const opName in parsedObj["op_defs"]) {
                    // console.log("opname:", opName);
                    let substPairs = substs.map(s => [s.namedChildren[0].text, {"node":s.namedChildren[2], "curr_defs_context": _.keys(op_defs)}]);
                    let identitySubstPairs = allNonSubDecls.map(d => [d, {"node": null, "curr_defs_context": _.keys(op_defs), "identity": true}]);
                    // console.log(substPairs);
                    let currentSubs = parsedObj["op_defs"][opName]["substitutions"];
                    
                    // Add any new substitutions to already existing set of substitutions for this definition.
                    parsedObj["op_defs"][opName]["substitutions"] = _.merge(currentSubs, _.fromPairs(substPairs), _.fromPairs(identitySubstPairs));
                }

                //
                // Go ahead and add all definitions from this module to the
                // current module. 
                //
                // For namespaced instantiations, these are prefixed with the
                // name of the instance definition.
                //
                for (const opName in parsedObj["op_defs"]) {
                    // console.log("opname:", opName);
                    let origOpDef = parsedObj["op_defs"][opName];
                    let prefix = moduleDefName + "!";
                    // let substOpName = prefix + opName;
                    let substOpName = prefix + origOpDef.name;


                    let substPairs = substs.map(s => [s.namedChildren[0].text, { "node": s.namedChildren[2], "curr_defs_context": _.keys(op_defs) }]);
                    // console.log(substPairs);
                    let currentSubs = parsedObj["op_defs"][opName]["substitutions"];
                    // Add any new substitutions to already existing set of substitutions for this definition.
                    let newSubs = _.merge(currentSubs, _.fromPairs(substPairs));
                    // let newSubs = _.merge(currentSubs, _.fromPairs(substPairs), _.fromPairs(identitySubPairs));
                    // console.log("new subs:", parsedObj["op_defs"][opName]["substitutions"]);

                    // N.B. Notes on module semantics: https://lamport.azurewebsites.net/tla/newmodule.html
                    // IF we are evaluating an expression from a named module instantation (e.g. M!Expr), 
                    // then this expression should be able to refer to definitions that appear in the original module M.

                    // Any definitions that are available in the scope of this instantiated module
                    // should also be accessible to expressions that are evaluated in the namespaced
                    // context of this module.
                    let nextId = self.nextGlobalDefId();
                    op_defs[nextId] = {
                        "id": nextId,
                        "name": substOpName,
                        "args": origOpDef.args,
                        "node": origOpDef.node,
                        "name_prefix": prefix,
                        "parent_module_name": root_mod_name,
                        "substitutions": newSubs,
                        // "module_defs": parsedObj["op_defs"],
                        "module_param_args": paramModArgs,
                        "curr_defs_context": origOpDef["curr_defs_context"]
                    };
                    // self.globalDefTable[substOpName] = op_defs[substOpName];
                    self.globalDefTable[nextId] = op_defs[nextId];
                }
                console.log("op defs:", op_defs)
            }

            // CONSTANT c1, c2, c3
            if (node.type === "constant_declaration") {
                let constDecls = cursor.currentNode().namedChildren.filter(isNotCommentNode);
                for (const declNode of constDecls) {
                    let constDeclName = null;
                    if (declNode.type === "operator_declaration") {
                        // e.g. CONSTANT Op(_,_)
                        // Just save the operator name directly.
                        constDeclName = declNode.childForFieldName("name").text;
                    } else {
                        constDeclName = declNode.text
                    }
                    const_decls[constDeclName] = { "id": declNode.id };
                    evalLog("Added CONSTANT decl:", constDeclName, node.namedChildren);
                }
            }

            // VARIABLE x, y, z
            if (node.type === "variable_declaration") {
                let varDecls = cursor.currentNode().namedChildren.filter(isNotCommentNode);
                for (const declNode of varDecls) {
                    var_decls[declNode.text] = { "id": declNode.id };
                }
            }

            if(node.type === "recursive_declaration"){
                // console.log("RECURSIVE DECLARATION:", node);

                cursor.gotoFirstChild();

                // Drill down to the actual definition node for a LOCAL definition.
                let isLocalDef = (node.type === "local_definition");
                if(node.type === "local_definition"){
                    cursor.gotoNextSibling();
                    cursor.gotoFirstChild();
                }

                let infixOpSymbol = null;
                if(node.children[1].type === "infix_op_symbol"){
                    console.log("INFIX OP SYMBOL");
                    infixOpSymbol = node.children[1].text;
                    console.log(infixOpSymbol);
                }

                cursor.gotoNextSibling();

                // The definition identifier name.
                node = cursor.currentNode();
                console.log("NODE:", node);

                let opName = node.namedChildren[0].text;
                // console.log("OP NAME:", opName);
                let placeholders = node.namedChildren.filter(n => n.type === "placeholder");
                // console.log("PLACEHOLDERS:", placeholders);

                let parentModuleName = root_mod_name;
                let defUniqueId = self.nextGlobalDefId();

                op_defs[defUniqueId] = { 
                    "id": defUniqueId,
                    "name": opName, 
                    "args": placeholders, 
                    "node": null, 
                    "is_local": isLocalDef, 
                    "isInfix": infixOpSymbol !== null,
                    "var_decls_context": _.clone(var_decls),
                    // Store the current set of definitions that exist at the
                    // point of this definition. We store this simply as a set
                    // of keys, since we can look up these in the global
                    // definition table if needed.
                    "curr_defs_context": _.keys(op_defs),
                    // "op_def_object": defObject,
                    "recursive_declaration": true
                };

                // As we go through parsing of any module, we retain a global
                // table of all definitions encountered in any module, to
                // potentially be looked up later when evaluating definitions in
                // their current "context" i.e. the set of definitions that
                // existed at the time of their original definition.
                // self.globalDefTable[opName] = op_defs[opName];
                // self.globalDefTable[opName] = op_defs[defUniqueId];
                self.globalDefTable[defUniqueId] = op_defs[defUniqueId];
                // self.globalDefTableObj.addDefinition(opName, defObject);

                cursor.gotoParent();
                if(isLocalDef){
                    // Go up one extra level for LOCAL defs.
                    cursor.gotoParent();
                }

            }

            // E.g.
            // Expr == 5
            // LOCAL Expr == 6
            // console.log("NODE:", node);
            if (node.type === "operator_definition" || 
                (node.type === "local_definition" && node.children[1].type === "operator_definition")) {
                // console.log("LOCAL DEF SYMBOL", node);

                cursor.gotoFirstChild();

                // Drill down to the actual definition node for a LOCAL definition.
                let isLocalDef = (node.type === "local_definition");
                if(node.type === "local_definition"){
                    console.log("LOCAL DEF SYMBOL");

                    cursor.gotoNextSibling();
                    cursor.gotoFirstChild();
                }

                // console.log(node);
                let infixOpSymbol = null;
                if(node.children[1].type === "infix_op_symbol"){
                    console.log("INFIX OP SYMBOL");
                    infixOpSymbol = node.children[1].text;
                    console.log(infixOpSymbol);
                }

                // The definition identifier name.
                node = cursor.currentNode()

                // console.log(node.text, node)
                // console.log(cursor.currentFieldName());
                assert(node.type === "identifier");
                let opName = node.text;

                if(infixOpSymbol !== null){
                    opName = infixOpSymbol;
                }

                let parentModuleName = root_mod_name;
                let defUniqueId = self.nextGlobalDefId();

                op_defs[defUniqueId] = { 
                    "id": defUniqueId,
                    "name": opName, 
                    "args": [], 
                    "node": null, 
                    "is_local": isLocalDef, 
                    "isInfix": infixOpSymbol !== null,
                    "var_decls_context": _.clone(var_decls),
                    "parent_module_name": root_mod_name,
                    // Store the current set of definitions that exist at the
                    // point of this definition. We store this simply as a set
                    // of keys, since we can look up these in the global
                    // definition table if needed.
                    "curr_defs_context": _.keys(op_defs),
                };

                // If a previously defined RECURSIVE operator exists with a matching name in the current context, 
                // record a pointer to us.
                let prevRecOp = _.find(op_defs, o => o.name === opName && o.recursive_declaration);
                if(prevRecOp !== undefined){
                    op_defs[prevRecOp.id]["recursive_definition_id"] = defUniqueId;
                }


                // As we go through parsing of any module, we retain a global
                // table of all definitions encountered in any module, to
                // potentially be looked up later when evaluating definitions in
                // their current "context" i.e. the set of definitions that
                // existed at the time of their original definition.
                self.globalDefTable[defUniqueId] = op_defs[defUniqueId];
                evalLog("added def:", op_defs[defUniqueId]);

                // Skip the 'def_eq' symbol ("==").
                if(infixOpSymbol === null){
                    cursor.gotoNextSibling();
                    if (!cursor.currentNode().isNamed()) {
                        cursor.gotoNextSibling();
                    }
                }

                // n-ary operator. save all parameters.
                while (cursor.currentFieldName() === "parameter") {
                    let currNode = cursor.currentNode();
                    // console.log("PARAMETER: ", currNode.text)
                    // console.log("PARAMETER: ", currNode.namedChildren[0])

                    //
                    // Note that we may be handling a higher order operator here, which can appear of the form
                    // Op2(l(_,_), a, b) == ...
                    //
                    // Regardless, we save the whole parameter node.
                    //
                    if(currNode.type === "identifier" && var_decls.hasOwnProperty(currNode.text)){
                        // Ignore variables.
                        throw new Error("Operator parameter symbol '" + currNode.text + "' conflicts with previous VARIABLE declaration.");
                    }
                    op_defs[defUniqueId]["args"].push(currNode);

                    cursor.gotoNextSibling();
                    if (!cursor.currentNode().isNamed()) {
                        cursor.gotoNextSibling();
                    }
                    if(infixOpSymbol !== null && cursor.currentFieldName() === "name"){
                        cursor.gotoNextSibling();
                    }
                }

                // Skip any intervening comment nodes.
                cursor.gotoNextSibling();
                while (isCommentNode(cursor.currentNode())) {
                    cursor.gotoNextSibling();
                }

                // We should now be at the definition node.
                // console.log(cursor.currentNode().text)
                let def = cursor.currentNode();
                // console.log("def type:", def.type);
                // console.log("def type:", def);

                // console.log(cursor.currentNode());
                // let var_ident = cursor.currentNode();
                cursor.gotoParent();
                if(isLocalDef){
                    // Go up one extra level for LOCAL defs.
                    cursor.gotoParent();
                }
                // Save the variable declaration.
                // var_decls[var_ident.text] = {"id": node.id}; 
                op_defs[defUniqueId]["node"] = def;
                // console.log("opDef:", op_defs[opName]);
            }

            // e.g. F[x,y \in {1,2}, z \in {3,4}] == x + y + z
            if (node.type === "function_definition") {
                // TODO: Consider iterating through 'named' children only?
                cursor.gotoFirstChild();
                console.log("fn def named children:", node.namedChildren);

                let fnName = node.namedChildren[0].text;
                let quant_bounds = node.namedChildren.filter(n => n.type === "quantifier_bound");
                let fnDefNode = node;

                let parentModuleName = root_mod_name;
                let defUniqueId = self.nextGlobalDefId();

                // The definition identifier name.
                node = cursor.currentNode()
                console.log(node.text, node)
                // console.log(cursor.currentFieldName());
                // assert(node.type === "identifier");
                // let fnName = node.text;

                op_defs[defUniqueId] = { 
                    "id": defUniqueId,
                    "name": fnName, 
                    "quant_bounds": quant_bounds, 
                    "node": null,
                    "parent_module_name": parentModuleName,
                    // Store the current set of definitions that exist at the
                    // point of this definition. We store this simply as a set
                    // of keys, since we can look up these in the global
                    // definition table if needed.
                    "curr_defs_context": _.keys(op_defs),
                    "is_function": true
                };
                cursor.gotoParent();
                // Save the function definition.
                op_defs[defUniqueId]["node"] = fnDefNode;

                // As we go through parsing of any module, we retain a global
                // table of all definitions encountered in any module, to
                // potentially be looked up later when evaluating definitions in
                // their current "context" i.e. the set of definitions that
                // existed at the time of their original definition.
                self.globalDefTable[defUniqueId] = op_defs[defUniqueId];
            }

        }

        evalLog("module const declarations:", const_decls);
        evalLog("module var declarations:", var_decls);
        evalLog("module definitions:", op_defs);

        let objs = {
            "root_mod_name": root_mod_name,
            "const_decls": const_decls,
            "var_decls": var_decls,
            "op_defs": op_defs,
            "imported_op_defs": imported_op_defs,
            "extends_modules": extends_modules,
            "spec_rewritten": specTextRewritten,
            "rewriter": rewriter
        }

        return objs;
    }

}

/**
 * Defines an evaluation context structure for evaluating TLC expressions and
 * initial/next state generation.
 */
class Context {
    constructor(val, state, defns, quant_bound, constants, prev_func_val, operators_bound, module_table, 
                eval_node, substitutionsNew, module_eval_namespace_prefix, 
                var_decls_context, defns_curr_context, def_overrides) {

        // @type: TLAValue
        // The result value of a TLA expression, or 'null' if no result has been
        // computed yet.
        this.val = val;

        // @type: TLAState
        // Represents the current assignment of values to variables in an
        // in-progress expression evaluation i.e. simply a mapping from
        // variable names to TLA values.
        this.state = state;

        // Stores a global definition table that can be used to look up definitions across modules.
        this.global_def_table = null;

        this.spec_obj = null;

        // @type: Object
        // Global definitions that exist in the specification, stored as mapping
        // from definition names to their syntax tree node.
        this.defns = defns;

        // @type: Object
        // Map containing values of any instantiated constant parameters of the spec.
        this.constants = constants;

        // @type: string -> TLCValue
        // Currently bound identifiers in the in-progress expression evaluation,
        // stored as a mapping from identifier names to their TLC values.
        this.quant_bound = quant_bound;

        // Currently bound operators in the in-progress expression evaluation e.g.
        // those defined inside a LET-IN expressions.
        this.operators_bound = operators_bound || {};

        // @type: TLAValue
        // Stores a binding of a previous function value (e.g. the @ symbol) for 
        // EXCEPT based record updates.
        this.prev_func_val = prev_func_val;

        // Are we evaluating this expression inside a "primed" context i.e.
        // should we treat all non-constant expressions (e.g. state variables) 
        // as being primed.
        this.primed = false;

        // Mapping from module names to their parsed spec objects.
        this.module_table = module_table || {};

        this.eval_node = eval_node || null;

        this.substitutions = substitutionsNew;

        this.module_eval_namespace_prefix = module_eval_namespace_prefix;

        // Stores whether some variables were declared at the time of definition the original context of an expression.
        this.var_decls_context = var_decls_context;

        // Used to store the current set of definitions that existed (i.e. were
        // in scope) for a given definition.
        this.defns_curr_context = defns_curr_context;

        this.def_overrides = def_overrides || {};
    }

    setGlobalDefTable(global_def_table){
        this.global_def_table = global_def_table;
    }

    setSpecObj(spec_obj){
        this.spec_obj = spec_obj;
    }

    setDefOverrides(def_overrides){
        this.def_overrides = def_overrides;
    }

    getDefnInCurrContext(defnName) {
        return _.find(this.global_def_table, o => o.name === defnName && this["defns_curr_context"].includes(o.id));
    }

    hasDefnInCurrContext(defnName) {
        return this["defns_curr_context"] !== undefined &&
            this["defns_curr_context"].map(defid => this.global_def_table[defid].name).includes(defnName);
    }

    cloneDeepVal(){
        // Worked on optimizing these clones.
        return _.clone(this.val);
        // return _.cloneDeep(this.val);
    }

    cloneDeepState(){
        // Worked on optimizing these clones.
        return _.clone(this.state);
        // return _.cloneDeep(this.state);
    }

    cloneDeepQuantBound(){
        return _.clone(this.quant_bound);
    }

    cloneDeepOperatorsBound(){
        return _.cloneDeep(this.operators_bound);
    }

    /**
     * Return a copy of this Context object.
     * 
     * Avoids copying of 'defns' since we assume they should be global
     * definitions that never change.
     */
    clone() {
        // For diagnostics.
        let start = performance.now();

        let stateNew = this.cloneDeepState();
        let valNew = this.cloneDeepVal();
        let defnsNew = this.defns // don't copy this field.
        let quant_boundNew = this.cloneDeepQuantBound();
        let operators_boundNew = this.cloneDeepOperatorsBound();
        let constants = _.clone(this.constants);
        let module_tableNew = this.module_table; // should never be modified
        let prev_func_val = _.cloneDeep(this.prev_func_val);
        let eval_node = _.cloneDeep(this.eval_node);

        let substitutionsNew = _.cloneDeep(this.substitutions);
        let module_eval_namespace_prefix_new = _.cloneDeep(this.module_eval_namespace_prefix);
        let var_decls_context_new = _.clone(this.var_decls_context);
        let defns_curr_context_new = _.clone(this.defns_curr_context);
        // For diagnostics to measure clone time and its impact on eval performance.
        const duration = (performance.now() - start);
        cloneTime = cloneTime + duration;
        numClones = numClones + 1;

        let ctxNew = new Context(
            valNew, stateNew, defnsNew, quant_boundNew, constants, prev_func_val,
            operators_boundNew, module_tableNew,
            eval_node, substitutionsNew,
            module_eval_namespace_prefix_new, var_decls_context_new, defns_curr_context_new);
        ctxNew.setGlobalDefTable(this["global_def_table"]);
        ctxNew.setSpecObj(this.spec_obj);
        ctxNew.setPrimed(this.primed);
        ctxNew.setDefOverrides(this.def_overrides);
        return ctxNew;
    }

    /**
     * Returns a new copy of this context with 'val' and 'state' updated to the
     * given values.
     * 
     * Should be equivalent to calling ctx.withVal(valNew).withState(stateNew)
     * but goal is to be more efficient.
     * @param {TLCValue} valNew 
     * @param {TLAState} stateNew 
     */
    withValAndState(valNew, stateNew) {
        let ctxCopy = this.clone();
        ctxCopy["val"] = valNew;
        ctxCopy["state"] = stateNew;
        return ctxCopy;
    }


    /**
     * Returns a new copy of this context with 'val' updated to the given value.
     * @param {TLCValue} valNew 
     */
    withVal(valNew) {
        let ctxCopy = this.clone();
        ctxCopy["val"] = valNew;
        return ctxCopy;
    }

    /**
     * Returns a new copy of this context with 'state' updated to the given value.
     * @param {Object} stateNew 
     */
    withState(stateNew) {
        let ctxCopy = this.clone();
        ctxCopy["state"] = stateNew;
        return ctxCopy;
    }

    /**
     * Returns a new copy of this context with the value 'val' bound to 'name'.
     */
    withBoundVar(name, val) {
        let ctxCopy = this.clone();
        ctxCopy["quant_bound"][name] = val;
        return ctxCopy;
    }

    /**
     * Returns a new copy of this context with the operator 'op' bound to 'name'.
     */
    withBoundOp(name, op) {
        let ctxCopy = this.clone();
        ctxCopy["operators_bound"][name] = op;
        return ctxCopy;
    }

    withBoundDefn(name, def) {
        let ctxCopy = this.clone();
        ctxCopy["defns"][name] = def;
        return ctxCopy;
    }

    /**
     * Returns a new copy of this context that has been set to "primed".
     */
    withPrimed() {
        let ctxCopy = this.clone();
        ctxCopy.primed = true;
        return ctxCopy;
    }

    /**
     * Is this a "primed" evaluation context.
     */
    isPrimed() {
        return this.primed;
    }

    setPrimed(primed){
        this.primed = primed;
    }

    /**
     * Checks if an identifier is bound to a definition in some imported module.
     */
    getDefnBoundInModule(defn){
        for(const m in this.module_table){
            console.log(this.module_table[m]);
            let moduleDefs = this.module_table[m]["op_defs"];
            if(moduleDefs.hasOwnProperty(defn)){
                return moduleDefs[defn];
            }
        }
        return null;
    }

    hasOperatorBound(defName) {
        return this["defns"].hasOwnProperty(defName) || this["operators_bound"].hasOwnProperty(defName);
    }

    hasSubstitutionFor(identName){
        return this["substitutions"] !== undefined && this["substitutions"].hasOwnProperty(identName);
    }

    getBoundOperator(defName) {
        assert(this.hasOperatorBound(defName), `operator ${defName} not bound in context`);
        if (this["defns"].hasOwnProperty(defName)) {
            return this["defns"][defName];
        }
        if (this["operators_bound"].hasOwnProperty(defName)) {
            return this["operators_bound"][defName];
        }
    }
}

function isNotCommentNode(node){
    return !["comment", "block_comment"].includes(node.type)
}

function isCommentNode(node){
    return !isNotCommentNode(node);
}

function evalLnot(v, ctx) {
    evalLog("evalLnot: ", v);
    lval = evalExpr(v, ctx)[0]["val"];
    let retval = new BoolValue(!lval.getVal())
    evalLog("evalLnot retval: ", retval);
    return [ctx.withVal(retval)];
}

function evalLand(lhs, rhs, ctx) {
    assert(ctx instanceof Context);

    // Evaluate left to right.
    evalLog("## LAND - LHS:", lhs.text, ", RHS: ", rhs.text);
    let lhsEval = _.flattenDeep(evalExpr(lhs, ctx));
    evalLog("lhsEval:", lhsEval);
    if (!lhsEval[0]["val"].getVal()) {
        // Short-circuit.
        return lhsEval;
    }
    let rhsEval = lhsEval.map(lctx => {
        evalLog("rhs:", rhs.text);
        evalLog("lctx:", lctx);
        return evalExpr(rhs, lctx).map(actx => {
            return [actx.withValAndState((lctx["val"].and(actx["val"])), actx["state"])];
        })
    });
    return _.flattenDeep(rhsEval);
}

// Handle a set of returned contexts from a disjunctive evaluation and determine if they should
// be coalesced into a single value or all contexts should be maintained as separate evaluation branches.
function processDisjunctiveContexts(ctx, retCtxs, currAssignedVars) {
    // Deal with return contexts for existential quantifiers.
    if (retCtxs.length > 1) {

        // If an evaluation has returned multiple contexts, it must have been the
        // result of a disjunctive split somewhere along the way, and in this case,
        // each branch must return a boolean value. (IS THIS CORRECT???)
        evalLog("disj ret vals: ", retCtxs.map(c => c["val"]));
        assert(retCtxs.map(c => c["val"]).every(v => v instanceof TLAValue));
        assert(retCtxs.map(c => c["val"]).every(v => v instanceof BoolValue));

        // Did any of the sub-evaluation contexts assign a new value to a state variable?
        let assignedInSub = retCtxs.some(c => {
            let assignedVars = _.keys(c["state"].stateVars).filter(k => c["state"].stateVars[k] !== null)
            return assignedVars.length > currAssignedVars.length;
            // evalLog("assigned vars:",assignedVars);
            return assignedVars;
        });

        // If new variables were assigned in the sub-evaluation contexts, then we return all of the
        // generated contexts. If no new variables were assigned, then we return the disjunction of
        // the results.
        if (assignedInSub) {
            evalLog("Newly assigned vars, returning ", retCtxs);
            return retCtxs;
        } else {
            evalLog("No newly assigned vars.");
            let someTrue = retCtxs.map((c) => c["val"].getVal()).some(_.identity);
            evalLog("ctx.", ctx);

            return [ctx.withVal(new BoolValue(someTrue))]
        }
    }
    return retCtxs;
}

function evalLor(lhs, rhs, ctx) {
    assert(ctx instanceof Context);

    let currAssignedVars = _.keys(ctx["state"].stateVars).filter(k => ctx["state"].stateVars[k] !== null)

    // return {"val": false, "states": vars};
    evalLog("## LOR");
    evalLog("orig ctx:", ctx);
    // For all existing possible variable assignments split into
    // separate evaluation cases for left and right branch.
    let ctxLhs = evalExpr(lhs, ctx);
    evalLog("lhs ctx:", ctxLhs);
    let ctxRhs = evalExpr(rhs, ctx);

    let retCtxs = ctxLhs.concat(ctxRhs);

    return processDisjunctiveContexts(ctx, retCtxs, currAssignedVars);
    // return ctxLhs.concat(ctxRhs);
}

// Checks if a syntax tree node represents a primed variable.
function isPrimedVar(treeNode, ctx) {
    if (treeNode.children.length < 2) {
        return false;
    }
    let lhs = treeNode.children[0];
    let symbol = treeNode.children[1];
    evalLog("lhs text:", lhs.text);
    evalLog("ctx state:", ctx.state);
    return (treeNode.type === "bound_postfix_op" &&
        lhs.type === "identifier_ref" &&
        symbol.type === "prime" &&
        ctx.state.hasVar(lhs.text) && ctx.state.getVarVal(lhs.text) !== null);
}

// Recursively unrolls definitions until we reach an expression that no longer
// points to another definition.
function applyDefReduction(node, ctx) {
    evalLog("defReduction:", node, ctx);

    // let currDefNode = node;
    let currDefNode = node;
    let currDefCtx = ctx["defns_curr_context"];
    let currIdentName = currDefNode.text;

    while (currDefCtx !== undefined &&
        currDefCtx.map(defid => ctx.global_def_table[defid].name).includes(currIdentName)) {

        // Look up the def in the global module table.
        currDef = ctx.getDefnInCurrContext(currIdentName);

        // Look up the def in the global module table.
        currDefNode = currDef.node;
        assert(currDef.node !== undefined, "Could not find definition for identifier: " + currIdentName);
        // console.log("EVAL EQ defNode:", defNode);

        currDefCtx = currDef.curr_defs_context;
        currIdentName = currDef.node.text;
        evalLog("defReduction step:", currIdentName, currDef.node.text, currDef, ctx);
    }

    evalLog("defReduction return:", currDefNode);

    return currDefNode;

}

function evalEq(lhs, rhs, ctx) {
    assert(ctx instanceof Context);

    // Deal with equality of variable on left hand side.
    let identName = lhs.text;
    // console.log("identName:", identName, lhs);

    let lhsCtx = ctx.clone();

    // 
    // If this is a primed identifier, then we see if we need to look up the unprimed identifer name e.g.
    //
    // VARIABLE x
    // def = x
    // Init == def' = 2
    //
    // If 
    if (lhs.children.length > 1 && lhs.type === "bound_postfix_op" && lhs.children[1].type === "prime" && !isPrimedVar(lhs, ctx)) {
        let unprimedName = lhs.children[0].text;

        lhs = { text: unprimedName, type: "identifier_ref", children: [] };
        lhs = applyDefReduction(lhs, lhsCtx);
        // Now treat this a primed version of the reduced expression.
        lhs = { text: lhs.text + "'", type: "bound_postfix_op", children: [lhs, { text: "'", type: "prime" }] };
        identName = lhs.text;
    }

    // Check for identity substitutions.
    if (ctx.hasSubstitutionFor(identName) && ctx["substitutions"][identName].node === null && ctx["substitutions"][identName].hasOwnProperty("identity")) {
        subNode = { text: identName, type: "identifier_ref", children: [] };
        evalLog("Substituted identity node:", subNode.text, "for", identName);
        lhs = subNode;
        identName = subNode.text;
        lhsCtx = ctx.clone();
        lhsCtx["defns_curr_context"] = lhsCtx["substitutions"][identName]["curr_defs_context"];
    }

    // Check for substitutions that may re-define this identifier.
    // We recursively apply substitutions until we reach a fixpoint, 
    // to handle the case of transitive module imports.
    while (ctx.hasSubstitutionFor(identName) && ctx["substitutions"][identName].node !== null && ctx["substitutions"][identName].node.text !== identName) {
        let subNode = ctx["substitutions"][identName].node;
        evalLog("Substituted node:", subNode.text, "for", identName);
        evalLog(ctx["substitutions"][identName]);

        // The definition context for the substitution may be different from the
        // definition context for the overall expression being evaluated.
        lhsCtx = ctx.clone();
        lhsCtx["defns_curr_context"] = lhsCtx["substitutions"][identName]["curr_defs_context"];
        lhs = subNode;
        identName = subNode.text;
    }

    // If this is a primed variable identifier, then we also need to see if there is a substitution defined for it.
    if (lhs.children.length > 1 &&
        lhs.type === "bound_postfix_op" &&
        lhs.children[1].type === "prime"
    ) {
        let identName = lhs.children[0].text;
        let newLhs = null;
        while (ctx.hasSubstitutionFor(identName) &&
            ctx["substitutions"][identName].node !== null &&
            ctx["substitutions"][identName].node.text !== identName) {
            let subNode = ctx["substitutions"][identName].node;
            evalLog("Substituted node:", subNode.text, "for", identName);
            evalLog(ctx["substitutions"][identName]);

            // The definition context for the substitution may be different from the
            // definition context for the overall expression being evaluated.
            lhsCtx = ctx.clone();
            lhsCtx["defns_curr_context"] = lhsCtx["substitutions"][identName]["curr_defs_context"];
            newLhs = subNode;
            identName = newLhs.text;
        }

        // Re-prime the variable after we computed the substitutions.
        if (newLhs !== null) {
            lhs = { text: newLhs.text + "'", type: "bound_postfix_op", children: [newLhs, { text: "'", type: "prime" }] };
        }
    }


    // 
    // Even if a left hand side does not directly refer to a variable, it is
    // possible it may refer to a definition that ultimately resolves to a
    // variable reference. We check this via repeated reduction of the left
    // hand side expression.
    // 

    lhs = applyDefReduction(lhs, lhsCtx);
    identName = lhs.text;


    let isUnprimedVar = ctx.state.hasVar(identName) && !isPrimedVar(lhs, ctx);

    // if (!isUnprimedVar && !isPrimedVar(lhs, ctx) &&
    //     ctx["defns_curr_context"] !== undefined && ctx["defns_curr_context"].includes(identName)) {
    //     // console.log("EVAL EQ defns_curr_context:", ctx["defns_curr_context"]);

    //     // Look up the def in the global module table.
    //     let defNode = ctx.global_def_table[identName]["node"];
    //     assert(defNode !== undefined, "Could not find definition for identifier: " + identName);
    //     // console.log("EVAL EQ defNode:", defNode);

    //     isUnprimedVar = ctx.state.hasVar(defNode.text) && !isPrimedVar(defNode, ctx);
    //     if (isUnprimedVar || isPrimedVar(defNode, ctx)) {
    //         console.log("Updating lhs to defNode:", defNode.text);
    //         lhs = defNode;
    //         identName = defNode.text;
    //     }
    // }


    if (isPrimedVar(lhs, ctx) || (isUnprimedVar && !ASSIGN_PRIMED)) {
        // Update assignments for all current evaluation ctx.

        // If, in the current state assignment, the variable has not already
        // been assigned a value, then assign it.If it has already been assigned,
        // then check for equality.
        // Variable already assigned in this context. So, check for equality.
        if (ctx.state.hasVar(identName) && ctx.state.getVarVal(identName) !== null) {
            evalLog("Variable '" + identName + "' already assigned in ctx:", ctx);
            let rhsVals = evalExpr(rhs, ctx);
            assert(rhsVals.length === 1);
            let rhsVal = rhsVals[0]["val"]
            evalLog("rhsVal:", rhsVal);
            let lhsVals = evalExpr(lhs, ctx)[0]["val"];
            let boolVal = (lhsVals.fingerprint() === rhsVal.fingerprint())
            ctx.eval_node = new AbstractEvalNode("eq_" + lhs.text, "eq", [rhsVals[0].eval_node])
            return [ctx.withVal(new BoolValue(boolVal))];
        }

        // Variable not already assigned. So, update variable assignment as necessary.
        let stateUpdated = _.mapValues(ctx.state.getStateObj(), (val, key, obj) => {
            if (key === identName) {
                evalLog("Variable (" + identName + ") not already assigned in ctx:", ctx);
                evalLog("rhs:", rhs);
                evalLog("ctx.defns_curr_context:", ctx.defns_curr_context);
                let rhsVals = evalExpr(rhs, ctx.clone());
                assert(rhsVals.length === 1);
                let rhsVal = rhsVals[0]["val"];
                evalLog("Variable (" + identName + ") getting value:", rhsVal);
                let vret = (val === null) ? rhsVal : val;
                evalLog(vret);
                ctx.eval_node = new AbstractEvalNode("eq_" + lhs.text, "eq", [rhsVals[0].eval_node])
                return vret;
            }
            return val;
        });
        evalLog("state updated:", stateUpdated);
        evalLog("state updated current ctx:", ctx);
        return [ctx.withValAndState(new BoolValue(true), new TLAState(stateUpdated))];
    } else {
        evalLog(`Checking for equality of ident '${identName}' with '${rhs.text}'.`, ctx);

        // Evaluate left and right hand side.
        // evalLog("eq lhs:", lhs);
        let lhsVals = evalExpr(lhs, ctx.clone());
        assert(lhsVals.length === 1);
        let lhsVal = lhsVals[0]["val"];
        // console.log("Checking for eq, lhsVal", lhsVal);

        let rhsVals = evalExpr(rhs, ctx.clone());
        assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        // console.log("Checking for eq, rhsVal", rhsVal);

        // Check equality.
        // TODO: Update this equality check.
        const boolVal = lhsVal.fingerprint() === rhsVal.fingerprint();
        evalLog("Checking for, boolVal:", boolVal);

        // Return context with updated value.
        return [ctx.withVal(new BoolValue(boolVal))];
    }
}

// 
// Given a node E that could be the right hand side of an unchanged expression 
// UNCHANGED <E>, extract the set of variables identifier that E refers to.
// 
// This could, for example, be a simple variable name like:
//  
// VARIABLE v1
// 
// or a tuple of variables like:
// 
// UNCHANGED <<v1, v2, v3>>.
// 
// Or also be a tuple that contains definition references e.g.
// 
// def1 == v1
// def2 == <<v2>>
// UNCHANGED <<def1, v2>>
// 
// This function handles the (recursive) extraction of variables from such an expression.
// 
function extractUnchangedVarSet(ctx, unchangedVal) {
    evalLog("extracting vars from UNCHANGED node:", unchangedVal);

    // Recursively de-parenthesize if needed.
    if (unchangedVal.type === "parentheses") {
        return extractUnchangedVarSet(ctx, unchangedVal.namedChildren[0]);
    }

    if (unchangedVal.type === "tuple_literal") {
        // Handle case where tuple consists of identifier_refs.
        let tupleElems = unchangedVal.namedChildren
            .filter(c => !c.type.includes("angle_bracket"));
        let tupUnchangedVars = _.flatten(tupleElems.map(c => extractUnchangedVarSet(ctx, c)));
        return tupUnchangedVars;

    } else {
        // Assume identifier_ref node.
        assert(unchangedVal.type === "identifier_ref");

        let ident_name = unchangedVal.text;
        evalLog("UNCHANGED identifier_ref:", ident_name);

        // Also check for substitutions of this identifier ref.
        while (ctx.hasSubstitutionFor(ident_name) && ctx["substitutions"][ident_name].node !== null && ctx["substitutions"][ident_name].node.text !== ident_name) {
            let subNode = ctx["substitutions"][ident_name].node;
            evalLog("Substituted node:", subNode.text, "for", ident_name);
            evalLog(ctx["substitutions"][ident_name]);

            // The definition context for the substitution may be different from the
            // definition context for the overall expression being evaluated.
            lhsCtx = ctx.clone();
            lhsCtx["defns_curr_context"] = lhsCtx["substitutions"][ident_name]["curr_defs_context"];
            lhs = subNode;
            ident_name = subNode.text;
            unchangedVal = subNode;
        }

        evalLog("UNCHANGED sub lookup:", ident_name, ctx);


        // If this identifier is a definition in the current context, then 
        // look up the definition node, and recurse on it.
        if (ctx.hasDefnInCurrContext(ident_name)) {
            evalLog("EVAL defns_curr_context:", ctx["defns_curr_context"]);
            let defnVal = ctx.getDefnInCurrContext(ident_name);
            evalLog("unchanged defn: ", defnVal);
            return extractUnchangedVarSet(ctx, defnVal.node);
        }

        return [unchangedVal];
    }
}

function evalUnchanged(node, ctx) {
    evalLog("eval UNCHANGED:", node);

    // Extract set of unchanged variables, and then update state in current context accordingly.
    let unchangedVal = node.namedChildren[1];
    let unchangedVars = extractUnchangedVarSet(ctx, unchangedVal);
    evalLog("Extracted set of UNCHANGED vars: ", unchangedVars);

    for (const elem of unchangedVars) {
        // Assign the primed version of this variable identifer to the same
        // value as the unprimed version.
        let unprimedVarVal = evalExpr(elem, ctx)[0]["val"];
        evalLog("unprimed Val: ", unprimedVarVal);
        let primedVarName = elem.text + "'";
        ctx.state = ctx.state.withVarVal(primedVarName, unprimedVarVal);
    }

    return [ctx.withVal(new BoolValue(true))];
}

function evalBoundInfix_mul(node, lhs, rhs, ctx){
    evalLog("mul lhs:", lhs, lhs.text);
    let mulLhsVal = evalExpr(lhs, ctx);
    evalLog("mul lhs val:", mulLhsVal);
    let lhsVal = mulLhsVal[0]["val"];
    let rhsVal = evalExpr(rhs, ctx)[0]["val"];
    let outVal = lhsVal.getVal() * rhsVal.getVal();
    // console.log("mul overall val:", outVal);
    ctx.eval_node = {"children": [mulLhsVal.eval_node]}
    return [ctx.withVal(new IntValue(outVal))];
}

function evalBoundInfix_plus(node, lhs, rhs, ctx){
    evalLog("plus lhs:", lhs, lhs.text);
    let plusLhsVal = evalExpr(lhs, ctx);
    evalLog("plus lhs val:", plusLhsVal);
    let lhsVal = plusLhsVal[0]["val"];
    let rhsValVal = evalExpr(rhs, ctx)
    let rhsVal = rhsValVal[0]["val"];
    assert(lhsVal instanceof IntValue);
    assert(rhsVal instanceof IntValue);
    let outVal = lhsVal.plus(rhsVal);
    ctx.eval_node = new AbstractEvalNode("plus_" + node.text, "plus", [plusLhsVal[0].eval_node, rhsValVal[0].eval_node])
    // ctx.eval_node = {"children": [plusLhsVal[0].eval_node, rhsValVal[0].eval_node]}
    evalLog("plus ret context:", ctx);
    return [ctx.withVal(outVal)];    
}

// 'vars' is a list of possible partial state assignments known up to this point.
function evalBoundInfix(node, ctx) {
    assert(ctx instanceof Context);

    evalLog("evalBoundInfix:", node, ctx);

    // lhs.
    let lhs = node.children[0];
    // symbol.
    let symbol = node.children[1];
    // console.log("symbol:", node.children[1].type);
    // rhs
    let rhs = node.children[2];

    // Eval results can also return abstract evaluation tree object?

    // Multiplication
    if (symbol.type === "mul") {
        return evalBoundInfix_mul(node, lhs, rhs, ctx);
    }

    // Plus.
    if (symbol.type === "plus") {
        return evalBoundInfix_plus(node, lhs, rhs, ctx);
    }

    // Plus.
    if (symbol.type === "minus") {
        evalLog("minus lhs:", lhs, lhs.text);
        let minusLhsVal = evalExpr(lhs, ctx);
        evalLog("minus lhs val:", minusLhsVal);
        let lhsVal = minusLhsVal[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let outVal = lhsVal.minus(rhsVal);
        return [ctx.withVal(outVal)];
    }

    // Greater than.
    if (symbol.type === "gt") {
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let outVal = lhsVal.getVal() > rhsVal.getVal();
        return [ctx.withVal(new BoolValue(outVal))];
    }

    // Less than.
    if (symbol.type === "lt") {
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let outVal = lhsVal.getVal() < rhsVal.getVal();
        return [ctx.withVal(new BoolValue(outVal))];
    }

    // Greater than or equal.
    if (symbol.type === "geq") {
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let outVal = lhsVal.getVal() >= rhsVal.getVal();
        return [ctx.withVal(new BoolValue(outVal))];
    }

    // Less than or equal.
    if (symbol.type === "leq") {
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let outVal = lhsVal.getVal() <= rhsVal.getVal();
        return [ctx.withVal(new BoolValue(outVal))];
    }

    // Modulo
    if (symbol.type === "mod") {
        evalLog("mul lhs:", lhs, lhs.text);
        let mulLhsVal = evalExpr(lhs, ctx);
        evalLog("mul lhs val:", mulLhsVal);
        let lhsVal = mulLhsVal[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        // Javascript '%' is actually remainder, not modulo, so doesn't worka as desired
        // for negative numbers.
        let n = lhsVal.getVal();
        let d = rhsVal.getVal();
        let outVal = ((n % d) + d) % d
        // console.log("mul overall val:", outVal);
        return [ctx.withVal(new IntValue(outVal))];
    }

    // Division.
    if (symbol.type === "div") {
        evalLog("bound_infix_op, symbol 'div'");
        evalLog(lhs);
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = Math.floor(lhsVal.getVal() / rhsVal.getVal());
        // console.log("mul overall val:", outVal);
        return [ctx.withVal(new IntValue(outVal))];
    }

    if(symbol.type === "pow"){
        evalLog("bound_infix_op, symbol 'pow'");
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = Math.pow(lhsVal.getVal(), rhsVal.getVal());
        // console.log("mul overall val:", outVal);
        return [ctx.withVal(new IntValue(outVal))];       
    }

    // Disjunction.
    if (symbol.type === "lor") {
        return evalLor(lhs, rhs, ctx);
    }

    if (symbol.type === "land") {
        return evalLand(lhs, rhs, ctx);
    }

    // Implication.
    if (symbol.type === "implies") {
        // (a => b) <=> (~a \/ b)
        let a = evalExpr(lhs, ctx)[0]["val"];
        // Short circuit evaluation of implication.
        if (!a.getVal()) {
            return [ctx.withVal(new BoolValue(true))];
        }
        let b = evalExpr(rhs, ctx)[0]["val"];
        return [ctx.withVal(new BoolValue(!a.getVal() || b.getVal()))];
    }

    // <=>
    if (symbol.type === "iff") {
        // (a <=> b) <=> ((a => b) /\ (b => a))
        let a = evalExpr(lhs, ctx)[0]["val"];
        let b = evalExpr(rhs, ctx)[0]["val"];
        assert(a instanceof BoolValue);
        assert(b instanceof BoolValue);
        return [ctx.withVal(new BoolValue(a.getVal() === b.getVal()))];
    }

    // Equality.
    if (symbol.type === "eq") {
        // console.log("bound_infix_op, symbol 'eq', ctx:", JSON.stringify(ctx));
        evalLog("bound_infix_op -> (eq), ctx:", ctx);
        return evalEq(lhs, rhs, ctx);
    }

    // Inequality.
    if (symbol.type === "neq") {
        // console.log("bound_infix_op, symbol 'neq', ctx:", JSON.stringify(ctx));
        evalLog("bound_infix_op -> (neq), ctx:", ctx);

        let lident = lhs.text;
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        // console.log("Checking for inequality with var:", varName);
        let rhsVals = evalExpr(rhs, ctx);
        assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        let areUnequal = lhsVal.fingerprint() !== rhsVal.fingerprint();
        // console.log("inequality lhsVal:", lhsVal);
        // console.log("inequality rhsVal:", rhsVal);
        evalLog("inequality boolVal:", areUnequal);
        // Return context with updated value.
        return [ctx.withVal(new BoolValue(areUnequal))];
    }

    // Set membership.
    if (symbol.type === "in" || symbol.type === "notin") {
        // 
        // We can just treat '<expr> \in S' as '\E h \in S : <expr> = h'
        // 

        // Pass this through to eval bounded quantification logic so it can be
        // treated as a standard existential quantifier expression.
        let domainVal = evalExpr(rhs, ctx)[0]["val"];
        let quantifier = {type: "exists"};
        // Create a unique, dummy identifer name to serve as quant ident in '\E h \in S : <expr> = h' 
        let uniqIdentName = "set_in_ident_" + ctx.spec_obj.nextGlobalDefId()
        let quant_expr_fn = (boundContext) => {
            return evalEq(lhs, {type: "identifier_ref", text: uniqIdentName, children: [] }, boundContext);
        }
        let retCtxs = evalOverQuantBounds(ctx, [[uniqIdentName, domainVal.getElems()]], quant_expr_fn, quantifier);
        
        // Evaluate 'notin', making the assumption that these will never be
        // expressions that fork into a disjunctive context.
        if(symbol.type === "notin"){
            let retVal = !retCtxs.some(rctx => rctx["val"].getVal())
            return [ctx.withVal(new BoolValue(retVal))];
        }
        else{
            let currAssignedVars = _.keys(ctx["state"].stateVars).filter(k => ctx["state"].stateVars[k] !== null)
            return processDisjunctiveContexts(ctx, retCtxs, currAssignedVars);
        }

    }

    // Set intersection.
    if (symbol.type === "cap") {
        evalLog("bound_infix_op, symbol 'cap'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("cap lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("cap rhs:", rhsVal);
        assert(lhsVal instanceof SetValue);
        assert(rhsVal instanceof SetValue);
        return [ctx.withVal(lhsVal.intersectionWith(rhsVal))];
    }

    // Set union.
    if (symbol.type === "cup") {
        // console.log("bound_infix_op, symbol 'cup'");
        evalLog("bound_infix_op, symbol 'cup'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        evalLog(lhs);
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("cup lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("cup rhs:", lhsVal);
        assert(lhsVal instanceof SetValue);
        assert(rhsVal instanceof SetValue);
        return [ctx.withVal(lhsVal.unionWith(rhsVal))];
    }

    // Set minus.
    if (symbol.type === "setminus") {
        // console.log("bound_infix_op, symbol 'setminus'");
        evalLog("bound_infix_op, symbol 'setminus'");
        // TODO: Will need to figure out a more principled approach to object equality.
        evalLog(lhs);
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("setminus lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("setminus rhs:", lhsVal);
        assert(lhsVal instanceof SetValue);
        assert(rhsVal instanceof SetValue);
        return [ctx.withVal(lhsVal.diffWith(rhsVal))];
    }

    // Set product. ("\X" or "\times")
    if (symbol.type === "times") {

        // 
        // When evaluating something like {1,2} \X {3,4} \X {5,6}, this produces
        // the set of triples <<1,3,5>>, <<1,3,6>>, <<1,4,5>>, ...
        // Note this is different from the case where we have {1,2} \X ({3,4} \X {5,6})
        // which produces the set of pairs <<1,<<3,5>>>, <<1,<<3,6>>>, <<1,<<4,5>>>, ...
        // 

        //
        // Find the maximal list of "linear" time expressions i.e. those that
        // are not encapsulated by parentheses.
        //
        // Generate a list of nodes in times expression at 1 level of depth.
        // e.g. {1,2} \X ({3,4} \X {5,6}) \X {7,8} will consider {1,2}, ({3,4}
        // \X {5,6}), and {7,8} as the top level elements of the times
        // expression domains.
        //
        function extractLinearTimesExprs(node) {
            if (node.children.length < 2) {
                return [node];
            }
            let symbol = node.children[1];
            if (symbol.type === "times") {
                let timesLeft = node.namedChildren[0];
                let timesRight = node.namedChildren[2];
                let out = extractLinearTimesExprs(timesLeft);
                out.push(timesRight);
                return out;
            }
            return [node];
        }

        let timesExprs = extractLinearTimesExprs(lhs).concat([rhs])
        // console.log("timesExprs:", timesExprs.map(t => t.text));

        let timesExprVals = timesExprs.map(t => evalExpr(t, ctx)[0]["val"]);
        // console.log("timesExprVals:", timesExprVals);

        evalLog("bound_infix_op, symbol 'times'");
        let fullProdElems = cartesianProductOf(...timesExprVals.map(t => t.getElems())).map(e => new TupleValue(e));
        return [ctx.withVal(new SetValue(fullProdElems))];
    }

    // Enumerated set with dot notation e.g. 1..N
    if (symbol.type === "dots_2") {
        // Assume both operands evaluate to numbers.
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert(lhsVal instanceof IntValue);
        assert(rhsVal instanceof IntValue);
        let rangeVal = _.range(lhsVal.getVal(), rhsVal.getVal() + 1).map(x => new IntValue(x));
        return [ctx.withVal(new SetValue(rangeVal))];
    }

    // Set subset
    if (symbol.type === "subseteq") {
        evalLog("bound_infix_op, symbol 'subseteq'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("subseteq lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("subseteq rhs:", rhsVal);
        assert(lhsVal instanceof SetValue);
        assert(rhsVal instanceof SetValue);
        return [ctx.withVal(lhsVal.isSubsetOf(rhsVal))];
    }

    //
    // Infix operators from TLC.tla standard module.
    //

    // d :> e == [x \in {d} |-> e]
    if (symbol.type === "map_to") {
        evalLog("bound_infix_op, symbol 'map_to', ctx:", ctx);
        let lhs = node.namedChildren[0];
        let rhs = node.namedChildren[2];

        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];

        let fcnVal = new FcnRcdValue([lhsVal], [rhsVal]);
        return [ctx.withVal(fcnVal)];
    }

    // f @@ g == [x \in (DOMAIN f) \cup (DOMAIN g) |-> IF x \in DOMAIN f THEN f[x] ELSE g[x]]
    if (symbol.type === "compose") {
        evalLog("bound_infix_op, symbol 'compose', ctx:", ctx);
        let lhs = node.namedChildren[0];
        let rhs = node.namedChildren[2];

        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];

        // Cast tuples to be treated as functions if we are composing functions.
        if(lhsVal instanceof TupleValue){
            lhsVal = lhsVal.toFcnRcd()
        }
        if(rhsVal instanceof TupleValue){
            rhsVal = rhsVal.toFcnRcd();
        }

        return [ctx.withVal(lhsVal.compose(rhsVal))];
    }

    // e.g. <<1,2>> \o <<3,4,5>>
    if (symbol.type === "circ") {
        evalLog("bound_infix_op, symbol 'circ', ctx:", ctx);
        let lhs = node.namedChildren[0];
        let rhs = node.namedChildren[2];

        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        assert((lhsVal instanceof TupleValue) || (lhsVal instanceof FcnRcdValue) || (lhsVal instanceof StringValue));
        assert((rhsVal instanceof TupleValue) || (rhsVal instanceof FcnRcdValue) || (rhsVal instanceof StringValue));

        // If one of the values is a string, then they both must be.
        // This matches the behavior of how TLC deasl with sequence ops applied to strings.
        assert((lhsVal instanceof StringValue) === (rhsVal instanceof StringValue));

        if(lhsVal instanceof StringValue){
            assert((rhsVal instanceof StringValue));
            return [ctx.withVal(new StringValue(lhsVal.getVal() + rhsVal.getVal()))];
        }

        if (lhsVal instanceof FcnRcdValue) {
            lhsVal = lhsVal.toTuple();
        }
        if (rhsVal instanceof FcnRcdValue) {
            rhsVal = rhsVal.toTuple();
        }

        let newTupVal = lhsVal.concatTup(rhsVal);
        return [ctx.withVal(newTupVal)];
    }

    // Check for definitions in the current context.
    let symbolText = symbol.text;
    if (ctx.hasDefnInCurrContext(symbolText)) {
        // Look up the def in the global module table.
        // opDef = _.find(ctx.global_def_table, o => o.name === symbolText);
        opDef = ctx.getDefnInCurrContext(symbolText);
        assert(opDef !== undefined, "Could not find definition for identifier: " + symbolText);
        return evalUserBoundOp(node, opDef, ctx)

    }

    // Check for user-defined infix operators.
    // TODO: Is this still needed? May be superseded by the above logic.
    if (ctx.hasOperatorBound(symbolText)) {
        // console.log("OPBOUND:", symbolText);
        let opDefObj = ctx["defns"][symbolText];
        // console.log(opDef);
        // console.log(node);
        return evalUserBoundOp(node, opDefObj, ctx)
    }

    // Infix operators can also be bound to CONSTANT values.
    if (ctx["constants"] !== undefined && ctx["constants"].hasOwnProperty(symbolText) && !(ctx["constants"][symbolText] instanceof TLAValue)) {
        evalLog("Found constant definition for:", symbolText, ctx["constants"][symbolText]);
        opDef = ctx.getDefnInCurrContext(ctx["constants"][symbolText]);
        return evalUserBoundOp(node, opDef, ctx);
    }

    throw new Error("unsupported infix symbol: '" + symbol.text + "'");

}

function evalEnabled(node, ctx) {
    let rhs = node.childForFieldName("rhs");
    let rhsVal = evalExpr(rhs, ctx)[0]["val"];
    evalLog("rhs ENABLED: ", rhsVal);
    assert(rhsVal instanceof BoolValue);
    return [ctx.withVal(rhsVal)];
}

// M!Op
// Evaluation of an expression from a named module instantiation.
function evalPrefixedOp(node, ctx) {

    let lhs = node.children[0];
    let rhs = node.children[1];
    let modPrefix = lhs.text;

    // console.log("prefixed op lhs:", lhs.text);
    // console.log("prefixed op rhs:", rhs);
    // console.log("prefixed op rhs:", rhs.text);

    // Extract op name depending on operator with no arguments or multi-arg operator.
    // e.g. M!Op vs. M!Op(1,2)
    let opName = "";
    let opArgs = [];
    if (rhs.namedChildren.length > 0) {
        opName = rhs.namedChildren[0].text
        opArgs = rhs.namedChildren.slice(1);
    } else {
        opName = rhs.text
    }
    // console.log("opName, opArgs:", opName, opArgs, ctx, _.clone(ctx.defns_curr_context));

    // 
    // If there are parameterized module arguments, then we evaluate this expression in the context of module
    // M but with the substitutions parameterized on the argument values.
    // 
    // e.g. M(x, y) == INSTANCE simple_extends_M4 WITH Val <- x, ValB <- y * 5
    //
    // TODO: Eventually support parameterized instantiation properly at some point.
    // 

    // For an expression like M(11,12)!Op, this extracts the module arguments (11,12).
    let moduleNode = lhs.namedChildren[0].namedChildren[0].namedChildren;
    let paramArgVals = [];
    if (moduleNode.length > 1) {
        let paramModuleArgs = lhs.namedChildren[0].namedChildren[0].namedChildren.slice(1);
        // console.log("module paramModuleArgs:", paramModuleArgs);
        paramArgVals = paramModuleArgs.map(a => evalExpr(a, ctx)[0]["val"]);
    }
    // console.log("module paramArgVals:", paramArgVals);

    // If this is a parameterized module prefixed op, like M!Op(1,2), then we look up the 
    // definition just using M!Op, and deal with the parameter arguments separately.
    if(paramArgVals.length > 0){
        modPrefix = lhs.namedChildren[0].namedChildren[0].namedChildren[0].text + "!";
    }

    // See if there is an (imported) definition that exists for this operator given
    // this module prefixing.

    //
    // When evaluating a named module instantiation expresison like M!Op, we
    // should be allowed to have access to any definitions that are accessible
    // from within the original module M. For example, if M defines
    // 
    // e1 == 5
    // e2 == e1 + 1
    //
    // And we have an instance of M locally and try to evaluate M!e2, then during evaluation
    // of M!e2, we should have access to the definitions e1 from the original module M.
    //

    let prefixedOpName = modPrefix + opName;
    // console.log("prefixedOpName:", prefixedOpName);


    let opDef = null;

    if (ctx.hasOperatorBound(prefixedOpName)) {
        // console.log("found prefixed op name:", prefixedOpName);
        opDef = ctx.getBoundOperator(prefixedOpName);
    }

    // Definitions are defined with a "current context" i.e. the set of
    // variables, definitions, declarations that existed at the point of
    // original definition in a module. So, we see if this could be a module
    // based definition that we need to look up.
    // if(
    //     // ctx.defns_curr_context !== undefined && ctx.defns_curr_context.includes(prefixedOpName)
    //     ctx.hasDefnInCurrContext(prefixedOpName)
    // ){
    //     // Look up the def in the global module table.
    //     opDef = ctx.getDefnInCurrContext(prefixedOpName);
    //     // opDef = ctx.global_def_table[prefixedOpName];
    // }


    if (ctx.hasDefnInCurrContext(prefixedOpName)) {
        // Look up the def in the global module table.
        opDef = ctx.getDefnInCurrContext(prefixedOpName);
        assert(opDef !== undefined, "Could not find definition for identifier: " + prefixedOpName);
    }


    if (opDef !== null) {
        // console.log("found prefixed op name:", prefixedOpName);
        // opDef = ctx.getBoundOperator(prefixedOpName);
        // console.log(opDef);

        // Bind the given module arguments to the module parameters during evaluation of the prefixed op
        // expression.
        let moduleParamArgNames = opDef["module_param_args"].map(a => a.text);

        assert(moduleParamArgNames.length === paramArgVals.length, "Mismatch in number of module arguments and parameters.");
        for(let i = 0; i < moduleParamArgNames.length; i++){
            evalLog("binding module param arg:", moduleParamArgNames[i]," <- ", paramArgVals[i]);
            ctx = ctx.withBoundVar(moduleParamArgNames[i], paramArgVals[i]);
        }

        // If this identifier ref has any substitutions, then we
        // consider those in the context during evaluation.
        if (opDef.hasOwnProperty("substitutions")) {
            ctx["substitutions"] = opDef["substitutions"];
        }

        let newCtx = ctx.clone();

        // Evaluate this expression with access to definitions inside the original module.
        // TODO: Re-consider this as an approach to evaluating named module instantation definitions?
        // 
        // Note that all definitions from M should be imported locally with prefixed op name, so we should be able
        // to look up them in current context if we just prepend the proper prefix.
        // 
        // let modNsPrefix = lhs.text;

        // If this is a parameterized module prefixed op, like M!Op(1,2), 
        // then we extract the def name itself without the parameters.
        // if(lhs.children[0].children[0].type === "bound_op"){
        //     modNsPrefix = lhs.children[0].children[0].children[0].text + "!";
        // }
        // newCtx["module_eval_namespace_prefix"] = modNsPrefix;


        // If this is an operator with arguments, then we evaluate it accordingly.
        // e.g. M!Op(1,2)
        if (opArgs.length > 0) {
            evalLog("eval user bound op:", _.clone(newCtx.defns_curr_context));
            return evalUserBoundOp(rhs, opDef, newCtx);
        }

        // Definitions are defined with a "current context" i.e. the set of
        // definitions/declarations that existed at the point of original
        // definition in a module. So, we need to include these definitions in
        // the evaluation context.
        let origCurrDefns = _.clone(newCtx["defns_curr_context"]);
        if (opDef.hasOwnProperty("curr_defs_context")) {
            newCtx["defns_curr_context"] = _.clone(opDef["curr_defs_context"]);
        }
        let ret = evalExpr(opDef.node, newCtx);
        ret.map(c => c.defns_curr_context = origCurrDefns);
        return ret;

    }
}

function evalBoundPrefix(node, ctx) {
    let symbol = node.children[0];
    let rhs = node.children[1];
    evalLog("evalBoundPrefix: ", node.type, ", ", node.text, `, prefix symbol: '${symbol.type}' `, "ctx:", ctx);

    // ENABLED.
    if (symbol.type === "enabled") {
        return evalEnabled(node, ctx);
    }

    // UNION
    if (symbol.type === "union") {
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outSetVal = new SetValue([]);
        for (const elSet of rhsVal.getElems()) {
            outSetVal = outSetVal.unionWith(elSet);
        }
        return [ctx.withVal(outSetVal)];
    }

    // DOMAIN.
    if (symbol.type === "domain") {
        evalLog("DOMAIN op");
        evalLog(rhs);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];

        // Tuples are considered as functions with natural number domains.
        if (rhsVal instanceof TupleValue) {
            return [ctx.withVal(new SetValue(rhsVal.getDomain()))];
        }

        evalLog("rhsVal: ", rhsVal);
        let domainVal = new SetValue(rhsVal.getDomain());
        evalLog("domain val: ", domainVal);
        return [ctx.withVal(domainVal)];
    }

    if (symbol.type === "powerset") {
        evalLog("POWERSET op");
        evalLog(rhs);
        let rhsVal = evalExpr(rhs, ctx);
        evalLog("rhsVal: ", rhsVal);
        rhsVal = rhsVal[0]["val"];
        let powersetRhs = subsets(rhsVal.getElems());
        // console.log("powersetRhs:", powersetRhs);
        powersetRhs = powersetRhs.map(x => new SetValue(x));
        // evalLog("powerset:",powersetRhs);
        return [ctx.withVal(new SetValue(powersetRhs))];
    }
    if (symbol.type === "negative") {
        let rhsVal = evalExpr(rhs, ctx);
        rhsVal = rhsVal[0]["val"];
        return [ctx.withVal(new IntValue(-rhsVal))];
    }

    if (symbol.type === "lnot") {
        return evalLnot(rhs, ctx);
    }


    if (symbol.type === "unchanged") {
        evalLog("eval prefix op: UNCHANGED", node);
        // assert(false, "UNCHANGED under construction!");
        return evalUnchanged(node, ctx);


    }
}

function evalBoundPostfix(node, ctx) {
    let lhs = node.namedChildren[0];
    let symbol = node.namedChildren[1];

    evalLog("Bound POSTFIX:", node);
    if (symbol.type === "prime") {
        evalLog("Evaluating expression in PRIMED (') context");
        return evalExpr(lhs, ctx.withPrimed());
    }

    return;

}

function evalDisjList(parent, disjs, ctx) {
    assert(ctx instanceof Context);

    evalLog("eval: disjunction list!");

    let currAssignedVars = _.keys(ctx["state"].stateVars).filter(k => ctx["state"].stateVars[k] !== null)

    // Split into separate evaluation cases for each disjunct.

    // Also filter out any comments in this disjunction list.
    disjs = disjs.filter(isNotCommentNode);
    for (var i = 0; i < disjs.length; i++) {
        // Remove any inline/inner comment nodes as well.
        // e.g. \/ (* inline comment *) x = 2
        _.remove(disjs[i].children, isCommentNode);
    }

    let retCtxs = _.flattenDeep(disjs.map(disj => evalExpr(disj, ctx)));
    return processDisjunctiveContexts(ctx, retCtxs, currAssignedVars);
}

function evalConjList(parent, conjs, ctx) {
    assert(ctx instanceof Context);

    evalLog("evalConjList -> ctx:", ctx, conjs);

    // Initialize boolean value if needed.
    if (ctx["val"] === null) {
        ctx["val"] = new BoolValue(true);
    }

    let shortCircuit = true;

    // Filter out any comments contained in this conjunction.
    let conjs_filtered = conjs.filter(isNotCommentNode);
    for (var i = 0; i < conjs_filtered.length; i++) {
        // Remove any inline/inner comment nodes as well.
        // e.g. \/ (* inline comment *) x = 2
        _.remove(conjs_filtered[i].children, isCommentNode);
    }


    return conjs_filtered.reduce((prev, conj) => {
        let res = prev.map(ctxPrev => {
            // If this context has already evaluated to false, then the overall
            // conjunction list will evaluate to false, so we can short-circuit
            // the expression evaluation and terminate early.
            if (ctxPrev["val"].getVal() === false && shortCircuit) {
                return [ctxPrev];
            }

            return evalExpr(conj, ctxPrev).map(ctxCurr => {
                let conjVal = ctxCurr["val"].and(ctxPrev["val"]);
                return ctxCurr.withVal(conjVal);
            });
        });
        evalLog("evalConjList mapped: ", res);
        return _.flattenDeep(res);
    }, [ctx]);
}

function evalIdentifierRef(node, ctx) {
    assert(ctx instanceof Context);

    let ident_name = node.text;
    evalLog(`evalIdentifierRef, '${node.text}' context:`, ctx.clone(), "ident_name:", ident_name);
    // See if this identifier is an override definition.
    if(ctx.def_overrides.hasOwnProperty(ident_name)){
        let overrideExpr = ctx.def_overrides[ident_name];
        let overrideNode = parseExprToNode(overrideExpr);
        return evalExpr(overrideNode, ctx);
    }

    // If this identifier ref has any substitutions, then we
    // consider those in the context during evaluation.
    if(ctx.hasDefnInCurrContext(ident_name) && ctx.getDefnInCurrContext(ident_name).hasOwnProperty("substitutions")){
        ctx["substitutions"] = ctx.getDefnInCurrContext(ident_name)["substitutions"];
    }

    // Are we in a "primed" evaluation context.
    let isPrimed = ctx.isPrimed();

    if (ctx.hasSubstitutionFor(ident_name) && !node.hasOwnProperty("identity_sub")) {
        let subNode = ctx["substitutions"][ident_name].node;
        if (subNode === null && ctx["substitutions"][ident_name].hasOwnProperty("identity")) {
            subNode = { text: ident_name, type: "identifier_ref", children: [], identity_sub: true, id: 0 };
        }
        evalLog("Substituted identifier node:", subNode.text, subNode.id, "for", ident_name);
        if (ident_name === subNode.text) {
            subNode.identity_sub = true;
        }
        let newCtx = ctx.clone();
        if (ctx["substitutions"][ident_name].hasOwnProperty("curr_defs_context")) {
            newCtx["defns_curr_context"] = ctx["substitutions"][ident_name].curr_defs_context;
            // If we performed a substitution for an identifier, then we no
            // longer need to perform substitutions for that identifier when
            // evaluating the substituted expression.
            _.unset(newCtx["substitutions"], ident_name);
        }
        return evalExpr(subNode, newCtx);
    }

    // 
    // If this identifier refers to a variable, return the value bound to that
    // variable in the current context.
    //
    // Note: if this is a reference to a variable inside a context where the variable
    // was not yet declared, then we don't try to evaluate this a variable
    // reference e.g. it could simply be an operator parameter argument.
    // 
    let var_undefined_in_context =
        ctx.hasOwnProperty("var_decls_context") &&
        ctx["var_decls_context"] !== undefined &&
        _.keys(ctx["var_decls_context"]).length === 0;

        // TODO: Re-enable this more fine-grained check once we figure out to deal with
        // module imports/renames appropriately.
        // !_.has(ctx["var_decls_context"]
            // , ident_name);
        
    if (ctx.state.hasVar(ident_name) && !var_undefined_in_context) {

        // Unprimed variable.
        if (!isPrimed) {
            evalLog("variable identifier: ", ident_name);
            let var_val = ctx.state.getVarVal(ident_name);
            evalLog("var ident context:", ctx["state"], var_val);
            return [ctx.withVal(var_val)];
        }

        // Primed variable.
        if (isPrimed) {
            evalLog("variable identifier (primed): ", ident_name + "'");
            let var_val = ctx.state.getVarVal(ident_name + "'");
            evalLog("var ident context:", ctx["state"], var_val);
            return [ctx.withVal(var_val)];
        }
    }

    // Evaluate identifier for primed context version.
    if (ctx.state.hasVar(ident_name + "'") && isPrimed) {
        evalLog("variable identifier (primed): ", ident_name + "'");
        let var_val = ctx.state.getVarVal(ident_name + "'");
        evalLog("var ident context:", ctx["state"], var_val);
        return [ctx.withVal(var_val)];
    }

    // See if the identifier is bound to a value in the current context.
    // If so, return the value it is bound to.
    if (ctx.hasOwnProperty("quant_bound") && ctx["quant_bound"].hasOwnProperty(ident_name)) {
        let bound_val = ctx["quant_bound"][ident_name];
        evalLog("bound_val", bound_val);
        return [ctx.withVal(bound_val)];
    }

    // Definitions are always defined with a "current context" i.e. the set of
    // variables, definitions, declarations that existed at the point of
    // original definition in a module.
    evalLog("checking for named defn:", ident_name);
    if (ctx.hasDefnInCurrContext(ident_name)) {
        evalLog("Getting identifier from current defns_curr_context:", ctx["defns_curr_context"]);

        // Look up the def in the global module table.
        // let defNode = ctx.global_def_table[ident_name]["node"];
        let defObj = ctx.getDefnInCurrContext(ident_name);
        let defNode = defObj["node"];
        assert(defNode !== undefined, "Could not find definition for identifier: " + ident_name);

        let evalCtx = ctx.clone();
        let origCurrDefns = _.clone(evalCtx["defns_curr_context"]);

        // Pass current definition context into the evaluation context as necessary.
        if(defObj !== undefined && defObj.hasOwnProperty("curr_defs_context")){
            evalLog("New defns_curr_context for identifier:", defObj["curr_defs_context"]);
            evalCtx["defns_curr_context"] = defObj["curr_defs_context"];
        }

        // Handle function definition case.
        let ret;
        if (defNode.type === "function_definition") {
            let quant_bounds = defNode.namedChildren.filter(n => n.type === "quantifier_bound");
            let fexpr = _.last(defNode.namedChildren);
            evalLog("EVAL function literal inner.")

            ret = evalFunctionLiteralInner(evalCtx, quant_bounds, fexpr);
            evalLog("ret:", ret);
            evalLog("origCurrDefns:", origCurrDefns);
            ret.map(c => c.defns_curr_context = origCurrDefns);
        } else {
            ret = evalExpr(defNode, evalCtx);
        }

        evalLog("origCurrDefns:", origCurrDefns, ret);
        ret.map(c => c.defns_curr_context = origCurrDefns);
        return ret;
    }

    // See if this identifier is an instantiated CONSTANT symbol.
    //
    // Note: checking this after we check for quant_bound values helps ensure we don't improperly
    // look up a bound CONSTANT value that shares a name with an operator definition argument that was declared
    // BEFORE the CONSTANT declaration. Related to 904cc93.
    // 
    if (ctx["constants"] !== undefined && ctx["constants"].hasOwnProperty(ident_name)) {
        // Return the instantiated constant value.
        let constantVal = ctx["constants"][ident_name];
        return [ctx.withVal(constantVal)];
    }

    // TODO: Consider case of being undefined.

    // If this is an unknown identifer and we are in a context where we are evaluating model
    // values, we treat this a new model value.
    if (ctx.hasOwnProperty("evalModelVals") && ctx["evalModelVals"]) {
        return [ctx.withVal(new ModelValue(ident_name))];
    }
}

// 
// Takes a set of identifier names each mapped to their domains and evaluates
// expression contexts over cross product of all these domain values.
// 
// Can also pass 'quant_expr' as a function which takes in a context bound with 
// quantified identifier and evaluates expression in this context.
// 
function evalOverQuantBounds(ctx, quantIdentAndDomains, quant_expr, quantifier){

    let allDomains = quantIdentAndDomains.map(identAndDomain => identAndDomain[1]);
    domainProduct = cartesianProductOf(...allDomains);
    // console.log("allDomains:", allDomains);
    // console.log("domainProduct:", domainProduct);

    // Trivial case of empty domain.
    if (domainProduct.length === 0) {
        // console.log("TRIVIAL CASE OF EMPTY DOMAIN");
        // \forall x \in {} : <expr> is always true.
        // \exists x \in {} : <expr> is always false.
        let retVal = (quantifier.type === "forall");
        return [ctx.withVal(new BoolValue(retVal))];
    }

    let retCtxs = domainProduct.map(domainVals => {
        let boundContext = ctx.clone();
        // Bound values to quantified variables.
        if (!boundContext.hasOwnProperty("quant_bound")) {
            boundContext["quant_bound"] = {};
        }
        for(var i = 0; i < domainVals.length; i++){
            let quantIdent = quantIdentAndDomains[i][0];
            // console.log("quantIdent:", quantIdent);

            // If quantIdent is a list of identifiers, this came from a
            // tuple_of_identifiers, and we bind each tuple identifier
            // accordingly.
            if (quantIdent instanceof Array) {
                for (var ind = 0; ind < quantIdent.length; ind++) {
                    boundContext["quant_bound"][quantIdent[ind]] = domainVals[i].getValues()[ind];
                }
            } else {
                boundContext["quant_bound"][quantIdent] = domainVals[i];
            }
        }            
        // evalLog("quantDomain val:", domVal);
        if(typeof quant_expr === 'function'){
            return quant_expr(boundContext);
        }
        let ret = evalExpr(quant_expr, boundContext);
        return ret;
    })

    return _.flattenDeep(retCtxs);
}

function evalBoundedQuantification(node, ctx) {
    evalLog("bounded_quantification", node);

    //
    // Bounded quantification expression in general form is like the following:
    //
    // \E i,j,k \in S, c,d \in T ... 
    //
    // Overall it will simply become a list of identifiers, each mapped to the domain (set of values) 
    // they are quantified over.
    // 
    let quantBoundNodes = node.namedChildren.filter(c => c.type === "quantifier_bound");
    // console.log("quantBoundNodes:", quantBoundNodes);
    
    // We now produce a list containing tuples of (identifier, domain) pairs.
    quantIdentsWithDomains = quantBoundNodes.map(q => {
        // \E i,j,k \in S, c,d \in T ... 
        // Remove the last 2 elements (the '\in' and the set expression)
        let setExpr = q.namedChildren.at(-1);
        let domainVal = evalExpr(setExpr, ctx)[0]["val"];
        assert(domainVal instanceof SetValue);
        let quantDomain = domainVal.getElems();

        let identifiers;
        // Also handle tuple identifier cases e.g. \E <<i,j>> \in S In this
        // case, each tuple identifier is bound to the correspondingtuple entry
        // of each value in the domain S.
        if (q.namedChildren[0].type === "tuple_of_identifiers"){
            console.log("tuple_of_identifiers", q.namedChildren[0]);
            let tupleOfIdents = q.namedChildren[0];
            // Store tuple identifiers as a list of identifiers.
            identifiers = [tupleOfIdents.namedChildren.filter(c => c.type === "identifier").map(c => c.text)];
        } else{
            identifiers = q.namedChildren.slice(0, -2).map(c => c.text);
        }
        return identifiers.map(i => [i, quantDomain]);
    })

    quantIdentsWithDomains = _.flatten(quantIdentsWithDomains);

    // console.log("quantIdentsWithDomains:", quantIdentsWithDomains);

    let quantifier = node.namedChildren[0];
    assert(quantifier.type === "exists" || quantifier.type === "forall");

    // The quantified expression.
    let quant_expr = node.namedChildren.at(-1); //[currInd];
    let currAssignedVars = _.keys(ctx["state"].stateVars).filter(k => ctx["state"].stateVars[k] !== null)

    // Now evaluate the quantified expression over all possible identifier value combinations.
    let retCtxs = evalOverQuantBounds(ctx, quantIdentsWithDomains, quant_expr, quantifier);

    // If this is a universal quantifier, then we don't fork the evaluation.
    if (quantifier.type === "forall") {
        let allVals = retCtxs.map(c => c["val"].getVal());
        evalLog("allVals:", allVals);
        let res = _.every(retCtxs.map(c => c["val"].getVal()));

        // For universal quantifiers, it is also valid for them to modify the
        // value of state variables inside their quantified expressions e.g. \A
        // s \in {3,4} : x' = 2. To address this, we return the latest context
        // produced as a result of evaluating the quantified expression (i.e. as
        // if it were the last conjunct in a conjunction).
        return [_.last(retCtxs).withVal(new BoolValue(res))];
    }

    assert(quantifier.type === "exists");
    return processDisjunctiveContexts(ctx, retCtxs, currAssignedVars);
}

// Evaluate a user defined n-ary operator application.
function evalUserBoundOp(node, opDefObj, ctx){
    evalLog("evalUserBoundOp:", node, opDefObj);

    let opDefNode = opDefObj["node"];   
    let opArgs = opDefObj["args"];
    let var_decls_context = opDefObj["var_decls_context"];

    let opArgNodes = node.namedChildren.slice(1);

    if(node.type === "bound_infix_op"){
        opArgNodes = [node.namedChildren[0], node.namedChildren[2]];
    }

    // n-ary operator.
    // Evaluate each operator argument.
    let opArgsEvald = opArgNodes.map(arg => {
        // Handle possible LAMBDA arguments which are supported for higher order operator
        // definitions.
        if (arg.type === "lambda") {
            // Don't evaluate LAMBA expressions, but record their nodes.
            return arg;
        }

        if (arg.type === "identifier_ref") {
            // Also possible that a reference to a pre-defined operator is passed as an argument
            // e.g.
            //
            // Plus(a,b) == a + b
            // Op(F(_,_)) == F(2,3)
            // val == Op(Plus)
            //

            // Check if this identifier is bound to an operator definition in the current
            // context i.e. check if it is an >= 1 arity operator.
            let ident_name = arg.text;
            if (ctx.hasDefnInCurrContext(ident_name) &&
                ctx.getDefnInCurrContext(ident_name)["args"].length > 0) {
                return arg;
            }
        }

        return evalExpr(arg, ctx)
    });
    let opArgVals = _.flatten(opArgsEvald);
    evalLog("opArgVals:", opArgVals);

    // Then, evaluate the operator defininition with these argument values bound
    // to the appropriate names.
    let opEvalContext = ctx.clone();
    if (!opEvalContext.hasOwnProperty("quant_bound")) {
        opEvalContext["quant_bound"] = {};
    }

    // If the operator definition has a context of variable declarations, then we need to
    // propagate this to the evaluation context so that we can correctly identify undefined
    // variables in the operator definition.
    if(var_decls_context !== undefined){
        opEvalContext["var_decls_context"] = var_decls_context;
        evalLog("opEvalContext with var_decls_context:", opEvalContext);
    }

    let origQuantBounds = _.clone(opEvalContext["quant_bound"]);

    evalLog("opDefNode", opDefNode);
    for (var i = 0; i < opArgs.length; i++) {
        // The parameter name in the operator definition.
        let paramName = opArgs[i].text;
        // console.log("paramName:", paramName);
        // console.log("paramName:", opArgs[i]);

        let anonOpArgName;
        let placeholders;
        if (opArgVals[i].type === "lambda" || opArgVals[i].type === "identifier_ref") {
            // Get the name of anonymous operator arg e.g. would be 'F' in the following definition.
            // Op1(F(_), v) == ....
            anonOpArgName = opArgs[i].namedChildren[0].text;

            // The underscores (_) that act as anonymous placeholders for operator arguments.
            placeholders = opArgs[i].namedChildren.filter(c => c.type === "placeholder");
        }

        if (opArgVals[i].type === "identifier_ref") {
            // Pre-defined operator that is used as an argument to a higher order operator definition.
            // So, we just use the existing operator definition (assuming it exists) and bind it with a new name.
            let opDefName = opArgVals[i].text;

            let opDef = ctx.getDefnInCurrContext(opDefName);

            let op = { "name": anonOpArgName, "args": opDef["args"], "node": opDef["node"] };
            opEvalContext["operators_bound"][anonOpArgName] = op;

            let lambdaOpId = opEvalContext.spec_obj.nextGlobalDefId();
            opEvalContext.global_def_table[lambdaOpId] = op;
            opEvalContext["defns_curr_context"].push(lambdaOpId);
        } else if (opArgVals[i].type === "lambda") {
            // For LAMBDA arguments, we need to bind their op definitions.
            let lambdaOp = opArgVals[i];
            let lambdaArgs = lambdaOp.namedChildren.filter(c => c.type === "identifier");
            let lambdaBody = lambdaOp.namedChildren[lambdaOp.namedChildren.length - 1];

            assert(placeholders.length === lambdaArgs.length,
                `LAMBDA argument count of ${lambdaArgs.length} must match anonymous operator arg count of ${placeholders.length}.`)

            // Note: LAMBDAs effectively capture the defs that exist in their
            // scope, since they may be evaluated lazily, later on.
            let lambdaOpId = opEvalContext.spec_obj.nextGlobalDefId();
            let op = { "name": anonOpArgName, "args": lambdaArgs, "node": lambdaBody, "id": lambdaOpId, "defns_curr_context": opEvalContext["defns_curr_context"], "lambda": true };
            opEvalContext["operators_bound"][anonOpArgName] = op;

            opEvalContext.global_def_table[lambdaOpId] = op;
            opEvalContext["defns_curr_context"].push(lambdaOpId);
        } else {
            opEvalContext["quant_bound"][paramName] = opArgVals[i]["val"];
        }

    }

    let origCurrDefns = _.clone(opEvalContext["defns_curr_context"]);
    if(opDefObj !== undefined && opDefObj.hasOwnProperty("curr_defs_context")){
        opEvalContext["defns_curr_context"] = opDefObj["curr_defs_context"];
    }

    // If we are evaluating a bound operator that was originally defined as a lambda function, then we need to evaluate the
    // operator with the definition context of the original lambda function.
    if (opDefObj !== undefined && opDefObj.hasOwnProperty("lambda")) {
        opEvalContext["defns_curr_context"] = opEvalContext["defns_curr_context"].concat(opDefObj["defns_curr_context"]);
    }

    ret = evalExpr(opDefNode, opEvalContext);

    // Don't retain these var decl context values in the context upon return. We
    // only need to evaluate specificially this user bound op with the
    // appropriate variable declaration context and we don't want this to
    // propagate through to other evaluation contexts upon return.
    ret.map(c => c.var_decls_context = undefined);
    ret.map(c => c.defns_curr_context = origCurrDefns);
    ret.map(c => c.quant_bound = origQuantBounds);

    // console.log("orig quant bounds:", origQuantBounds, opEvalContext["quant_bound"]);
    
    return ret;
}

// <op>(<arg1>,...,<argn>)
function evalBoundOp(node, ctx) {
    assert(node.type === "bound_op");

    let opName = node.namedChildren[0].text;
    evalLog("bound_op:", opName);
    evalLog("bound_op context:", ctx);

    //
    // Operators from the TLA+ Standard Modules.
    //
    // Treat these all as built-in operators for now.
    //

    if (opName == "Assert") {
        const conditionExpr = node.namedChildren[1];
        const conditionVal = evalExpr(conditionExpr, ctx)[0]["val"];
        assert(conditionVal instanceof BoolValue, "'Assert' expects a boolean expression.");
        if (conditionVal.getVal()) {
            return [ctx.withVal(conditionVal)];
        }
        let messageText = "";
        if (node.namedChildren.length >= 3) {
            const messageVal = evalExpr(node.namedChildren[2], ctx)[0]["val"];
            if (messageVal instanceof StringValue) {
                messageText = messageVal.getVal();
            } else if (messageVal !== undefined && messageVal !== null) {
                messageText = messageVal.toString();
            }
        }
        const errorMessage = messageText ? `TLC Assert failed: ${messageText}` : "TLC Assert failed.";
        throw new Error(errorMessage);
    }

    // FiniteSets 
    // https://github.com/tlaplus/tlaplus/blob/421bc3d16f869d9c9bb493e5950c445c25c916ea/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/FiniteSets.tla

    // Built in operator.
    if (opName == "Cardinality") {
        let argExpr = node.namedChildren[1];
        let argExprVal = evalExpr(argExpr, ctx)[0]["val"]
        evalLog("Cardinality val:", argExpr.text, argExprVal.length);
        return [ctx.withVal(new IntValue(argExprVal.size()))];
    }

    // Technically comes from 'FiniteSetsExt', but for now we implement it as a built-in operator.
    // TODO: When module semantics are fully worked out, we won't want to always include this a default operator.
    // if (opName == "Max") {
    //     let argExpr = node.namedChildren[1];
    //     let argExprVal = evalExpr(argExpr, ctx)[0]["val"];
    //     assert(argExprVal instanceof SetValue);
    //     assert(argExprVal.getElems().length > 0, "Cannot compute 'Max' of an empty set.");
    //     assert(argExprVal.getElems().every(e => e instanceof IntValue));

    //     // Compute the max.
    //     let intElems = argExprVal.getElems().map(e => e.getVal());
    //     evalLog("Max val:", argExpr.text, intElems);
    //     let maxVal = _.max(intElems);
    //     evalLog("Max val:", maxVal);
    //     return [ctx.withVal(new IntValue(maxVal))];
    // }

    // Sequences 
    // https://github.com/tlaplus/tlaplus/blob/421bc3d16f869d9c9bb493e5950c445c25c916ea/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Sequences.tla    

    if (opName == "Seq") {
        // TODO.
        throw new Exception("'Seq' operator unimplemented.");
    }

    if (opName == "Len") {
        let seqArgExpr = node.namedChildren[1];
        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"]

        // Handle string values upfront.
        if (seqArgExprVal instanceof StringValue) {
            return [ctx.withVal(new IntValue(seqArgExprVal.getVal().length))];
        }

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        assert(seqArgExprVal instanceof TupleValue);
        // evalLog("Append val:", seqArgExpr.text);
        return [ctx.withVal(new IntValue(seqArgExprVal.length()))];
    }

    if (opName == "SelectSeq") {
        let seqArgExpr = node.namedChildren[1];
        let selectLambda = node.namedChildren[2];

        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"];
        // console.log(selectLambda);

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        // For each element in the sequence, evaluate the lambda function on
        // that value.
        let lambdaArgs = selectLambda.namedChildren.filter(c => c.type === "identifier");
        let lambdaBody = selectLambda.namedChildren[selectLambda.namedChildren.length - 1];

        // console.log("lambda args:", lambdaArgs);
        // console.log("lambda body:", lambdaBody);

        let selectedRet = seqArgExprVal.getElems().filter(function(el){
            // let op = { "name": defVarName, "args": parameters, "node": defBody };
            // newBoundCtx = newBoundCtx.withBoundVar(defVarName, op);
            ret = evalExpr(lambdaBody, ctx.withBoundVar(lambdaArgs[0].text, el));
            return ret[0]["val"].getVal();
        });
        // console.log("filter ret:", selectedRet);

        assert(seqArgExprVal instanceof TupleValue);
        
        return [ctx.withVal(new TupleValue(selectedRet))];
    }

    // Append(seq, v)
    if (opName == "Append") {
        let seqArgExpr = node.namedChildren[1];
        let appendElemArgExpr = node.namedChildren[2];
        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"]

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        let appendElemArgExprVal = evalExpr(appendElemArgExpr, ctx)[0]["val"]

        assert(seqArgExprVal instanceof TupleValue);

        // evalLog("Append val:", seqArgExpr.text);
        return [ctx.withVal(seqArgExprVal.append(appendElemArgExprVal))];
    }

    if (opName == "Head") {
        let seqArgExpr = node.namedChildren[1];
        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"]

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        assert(seqArgExprVal instanceof TupleValue);
        // evalLog("Append val:", seqArgExpr.text);
        return [ctx.withVal(seqArgExprVal.head())];
    }

    if (opName == "Tail") {
        let seqArgExpr = node.namedChildren[1];
        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"]

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        assert(seqArgExprVal instanceof TupleValue);
        // evalLog("Append val:", seqArgExpr.text);
        return [ctx.withVal(seqArgExprVal.tail())];
    }

    if (opName == "SubSeq") {
        let seqArgExpr = node.namedChildren[1];
        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"]
        let startIndexExpr = node.namedChildren[2];
        let startIndexExprVal = evalExpr(startIndexExpr, ctx)[0]["val"]
        let endIndexExpr = node.namedChildren[3];
        let endIndexExprVal = evalExpr(endIndexExpr, ctx)[0]["val"]

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        assert(seqArgExprVal instanceof TupleValue);
        assert(startIndexExprVal instanceof IntValue);
        assert(endIndexExprVal instanceof IntValue);

        let startIndex = startIndexExprVal.getVal() - 1; // TLA is 1-indexed.
        let endIndex = endIndexExprVal.getVal(); // Note: end index is non-inclusive when using .slice()
        let subSeqElems = seqArgExprVal.getElems().slice(startIndex, endIndex);
        return [ctx.withVal(new TupleValue(subSeqElems))];
    }

    // Override this always to make it more efficient.
    if (opName == "SetToSeq") {
        // Custom operator.
        // Convert a set to some arbitrary but consistently chosen sequence of its elements.
        let argExpr = node.namedChildren[1];
        let argExprVal = evalExpr(argExpr, ctx)[0]["val"];
        assert(argExprVal instanceof SetValue);
        // assert(argExprVal.getElems().length > 0, "Cannot compute 'Max' of an empty set.");

        // TODO: Do we want/need to ensure a consistent ordering?
        // TODO: Sort elements by their hash, or string repr?
        return [ctx.withVal(new TupleValue(argExprVal.getElems()))];
    }

    // SortSeq(s, Op(_, _)) sorts a sequence 's' according to binary comparison operator 'Op'.
    if (opName == "SortSeq") {
        let seqArgExpr = node.namedChildren[1];
        let selectLambda = node.namedChildren[2];

        let seqArgExprVal = evalExpr(seqArgExpr, ctx)[0]["val"];

        // Try to interpret value as tuple, if possible.
        seqArgExprVal = seqArgExprVal.toTuple();

        // Sort the sequence according to the lambda function comparator.
        let lambdaArgs = selectLambda.namedChildren.filter(c => c.type === "identifier");
        let lambdaBody = selectLambda.namedChildren[selectLambda.namedChildren.length - 1];

        let seqElems = seqArgExprVal.getElems();
        seqElems.sort(function (a, b) {
            ret = evalExpr(lambdaBody, ctx.withBoundVar(lambdaArgs[0].text, a).withBoundVar(lambdaArgs[1].text, b));
            let compareVal = ret[0]["val"].getVal();
            return compareVal ? -1 : 1;
        });

        return [ctx.withVal(new TupleValue(seqElems))];
    }

    if (opName == "ToString") {
        let argExpr = node.namedChildren[1];
        let argExprVal = evalExpr(argExpr, ctx)[0]["val"]
        return [ctx.withVal(new StringValue(argExprVal.toString()))];
    }

    // Just treat TLCEval as a no-op in the web interpreter.
    if (opName == "TLCEval") {
        let argExpr = node.namedChildren[1];
        let argExprVal = evalExpr(argExpr, ctx)[0]["val"]
        return [ctx.withVal(argExprVal)];
    }

    // See if this is defined as via a CONSTANT assignment.
    let opDef = null;
    if (ctx["constants"] !== undefined && ctx["constants"].hasOwnProperty(opName) && !(ctx["constants"][opName] instanceof TLAValue)) {
        evalLog("Found constant definition for:", opName, ctx["constants"][opName]);
        opDef = ctx.getDefnInCurrContext(ctx["constants"][opName]);
        return evalUserBoundOp(node, opDef, ctx);
    }

    // Check for the bound op in the set of known definitions.
    if (ctx.hasDefnInCurrContext(opName)) {
        // Look up the def in the global module table.
        opDef = ctx.getDefnInCurrContext(opName);
        assert(opDef !== undefined, "Could not find definition for identifier: " + opName);

        // Look up the actualy definition for the recursive operator, not just the declaration.
        if (opDef.hasOwnProperty("recursive_declaration")) {
            evalLog("Looking up recursive definition for:", opDef);
            opDef = _.find(ctx.global_def_table, o => o.id === opDef.recursive_definition_id);
            assert(opDef !== undefined, "Could not find definition for recursive declaration: " + opName);
        }
    } else if (ctx["operators_bound"].hasOwnProperty(opName)) {
        opDef = ctx["operators_bound"][opName];
    } else if (ctx.getDefnBoundInModule(opName) !== null) {
        opDef = ctx.getDefnBoundInModule(opName);
    }
    else {
        // Unknown operator.
        throw new Error("Error: unknown operator '" + opName + "'.");
    }

    let opDefObj = opDef;
    evalLog("defns", node);
    evalLog("opDefObj", opDefObj);
    return evalUserBoundOp(node, opDefObj, ctx);

    // Unknown operator.
    throw new Error("Error: unknown operator '" + opName + "'.");

}

function evalFiniteSetLiteral(node, ctx) {
    // Remove the outer braces, "{" and "}"
    let innerChildren = node.children.slice(1, node.children.length - 1);
    // Remove commas and then evaluate each set element.
    let ret = innerChildren.filter(child => child.type !== ",")
    ret = ret.map(child => {
        // TODO: For now assume set elements don't fork evaluation context.
        let r = evalExpr(child, ctx);
        assert(r.length === 1, "Expected set elements not to fork evaluation");
        return r[0]["val"];
    });
    return [ctx.withVal(new SetValue(ret))];
}

/**
 * Compute all mappings from 'domain' to 'range'
 */
function combs(domain, range) {
    if (domain.length === 0) {
        // An empty domain gives us a single "empty" mapping.
        // Use lists of key-value pairs to represent mappings.
        return [[]];
    }
    let out = [];
    for (const v of range) {
        // Recursively compute combinations for the rest of the domain.
        for (const c of combs(domain.slice(1), range)) {
            c.push([domain[0], v])
            out.push(c);
        }
    }
    return out;
}

function evalSetOfFunctions(node, ctx) {

    // console.log("set_of_functions", node);

    // Domain.
    let Dval = evalExpr(node.namedChildren[0], ctx)[0]["val"];
    // Range.
    let Rval = evalExpr(node.namedChildren[2], ctx)[0]["val"];

    let Delems = Dval.getElems();
    let Relems = Rval.getElems();

    // Compute set of all functions from D -> R by first computing combinations 
    // with replacement i.e. choosing |D| elements from R.
    // 
    // e.g.
    // D : [a,b,c]
    // R : [1,2]
    // |[D -> R]| = 2^3 = 8
    //

    let combVals = combs(Delems, Relems);

    let fcnVals = [];
    for (var comb of combVals) {
        // Each combination should be a list of key-value pairs.
        let domainVals = comb.map(c => c[0]);
        let rangeVals = comb.map(c => c[1]);

        let fv = new FcnRcdValue(domainVals, rangeVals);
        fcnVals.push(fv);
    }

    return [ctx.withVal(new SetValue(fcnVals))];
}

function evalSetOfRecords(node, ctx) {
    let domainVals = [];
    let idents = [];
    for (var ind = 0; ind < node.namedChildren.length; ind += 2) {
        let ident = node.namedChildren[ind];
        idents.push(ident.text);
        let domain = node.namedChildren[ind + 1];
        let domainVal = evalExpr(domain, ctx)[0]["val"];
        assert(domainVal instanceof SetValue);
        evalLog(domainVal);
        domainVals.push(domainVal.getElems());
    }

    let domainTuples = cartesianProductOf(...domainVals);

    // Construct the set of records as the cartesian product of every field domain set.
    let outRecords = []
    for (var domainTuple of domainTuples) {
        let rcdDomain = idents.map(v => new StringValue(v));
        let rcdVals = domainTuple;
        let isRecord = true;
        let recordVal = new FcnRcdValue(rcdDomain, rcdVals, isRecord);
        outRecords.push(recordVal);
    }

    return [ctx.withVal(new SetValue(outRecords))];
}

// Evaluates a function literal definition at all elements in its domain.
// Accepts an optional argument 'domainVal' which limits evaluation to only
// compute function values at the given domain value.
function evalFunctionLiteralInner(ctx, quant_bounds, fexpr, selectedDomainVal) {
    evalLog("function_literal inner", fexpr, quant_bounds);

    //
    // TODO: Need to be able to handle function definitions like
    // sc[<<a, b>> \in (0 .. 5) \X (8 .. 12)] == a + b
    // 
    // Will need some fiddling of variable binding domains below.
    //
    let idents = quant_bounds.map(qb => {
        let domainVal = evalExpr(_.last(qb.namedChildren), ctx)[0]["val"];
        return qb.namedChildren
            .filter(n => n.type === "identifier")
            .map(x => [x, domainVal.getElems()]);
    });

    let domainIdents = _.flatten(idents).map(pair => pair[0]);
    let domainVals = _.flatten(idents).map(pair => pair[1]);
    let domainTuples = cartesianProductOf(...domainVals);

    // If a specific domain value was given, only evaluate at that domain value.
    if (selectedDomainVal !== undefined) {
        if (selectedDomainVal instanceof TupleValue) {
            selectedDomainVal = selectedDomainVal.getElems();
            domainTuples = [selectedDomainVal];
        } else {
            domainTuples = [[selectedDomainVal]];
        }
        evalLog("Evaluating function at selected domain val:", domainTuples)
    }

    evalLog("domainIdents:", domainIdents);
    evalLog("domainTuples:", domainTuples);

    let fcnArgs = domainTuples.map(t => (t.length === 1) ? t[0] : new TupleValue(t));
    let fcnVals = domainTuples.map(tuple => {
        // Evaluate function expression in appropriate context.
        let boundContext = ctx.clone();
        if (!boundContext.hasOwnProperty("quant_bound")) {
            boundContext["quant_bound"] = {};
        }
        for (var ind = 0; ind < domainIdents.length; ind++) {
            let identName = domainIdents[ind].text;
            boundContext["quant_bound"][identName] = tuple[ind];
        }
        evalLog("function_literal boundCtx:", boundContext);
        let vals = evalExpr(fexpr, boundContext);
        evalLog("fexpr vals:", vals);
        assert(vals.length === 1);
        return vals[0]["val"];
    });

    let newFnVal = new FcnRcdValue(fcnArgs, fcnVals);
    return [ctx.withVal(newFnVal)];
}

// "[" <quantifier_bound> "|->" <expr> "]"
function evalFunctionLiteral(node, ctx) {
    evalLog("function_literal: '" + node.text + "'");

    let quant_bounds = node.namedChildren.filter(n => n.type === "quantifier_bound");
    let fexpr = _.last(node.namedChildren);

    return evalFunctionLiteralInner(ctx, quant_bounds, fexpr);

}

function evalLetIn(node, ctx) {
    let opDefs = node.namedChildren.filter(c => c.type === "operator_definition");
    let fcnDefs = node.namedChildren.filter(c => c.type === "function_definition");
    let letInExpr = node.childForFieldName("expression");

    // Evaluate the expression with the bound definitions.
    let newBoundCtx = ctx.clone();
    let prevLetDefs = [];
    for (const def of opDefs) {
        let defVarName = def.childForFieldName("name").text;

        evalLog("LET IN def:", def);

        // Iterate over children until we hit equality symbol as a way to
        // extract op parameters.
        let parameters = [];
        for (const child of def.namedChildren.slice(1)) {
            if (child.type === "def_eq") {
                break;
            }
            parameters.push(child);
        }

        // Save the body of the defined operator.
        let defBody = def.childForFieldName("definition");

        evalLog("LET IN parameters:", parameters)

        // Bind as a new operator/definition in the context.
        let newLetDefId = newBoundCtx.spec_obj.nextGlobalDefId();
        let opDef = {
            "id": newLetDefId,
            "name": defVarName,
            "args": parameters,
            "node": defBody,
            "let_in_def": true
        };

        newBoundCtx.global_def_table[newLetDefId] = opDef;
        newBoundCtx.defns_curr_context.push(newLetDefId);

    }

    // Also support function definitions in LET-IN expressions.
    for (const def of fcnDefs) {
        let fnName = def.namedChildren[0].text;
        let quant_bounds = def.namedChildren.filter(n => n.type === "quantifier_bound");

        let newLetDefId = newBoundCtx.spec_obj.nextGlobalDefId();
        let fnDef = {
            "id": newLetDefId,
            "name": fnName,
            "quant_bounds": quant_bounds,
            "node": def,
            "is_function": true,
            "let_in_def": true
        };

        newBoundCtx.global_def_table[newLetDefId] = fnDef;
        newBoundCtx.defns_curr_context.push(newLetDefId);
    }
    evalLog("newBoundCtx:", newBoundCtx);
    return evalExpr(letInExpr, newBoundCtx);
}

// CHOOSE x \in {1,2} : P(x)
function evalChoose(node, ctx) {
    evalLog("CHOOSE", node);
    let boundVar = node.namedChildren[0];
    let domain = node.namedChildren[2];
    let condition = node.namedChildren[3];

    let domainVal = evalExpr(domain, ctx)[0]["val"];
    evalLog("CHOOSE domain:", domainVal);

    // Pick the first value in domain satisfying the condition.
    // TODO: Should ensure consistent iteration order i.e. by 
    // traversing in order sorted by element hashes.
    for (const val of domainVal.getElems()) {
        evalLog("CHOOSE domain val:", val);
        let boundCtx = ctx.withBoundVar(boundVar.text, val);
        let condVal = evalExpr(condition, boundCtx)[0]["val"];
        if (condVal.getVal()) {
            return [ctx.withVal(val)];
        }
    }

    // No value satisfying the CHOOSE.
    throw "No value satisfying CHOOSE predicate";
}

function evalExcept(node, ctx) {
    evalLog("EXCEPT node, ctx:", node, ctx);
    let lExpr = node.namedChildren[0];
    let updateExprs = node.namedChildren.filter(c => c.type === "except_update");
    let numUpdateExprs = updateExprs.length;

    evalLog("EXCEPT node:", node);
    evalLog("EXCEPT NAMED CHILDREN:", node.namedChildren);
    evalLog("EXCEPT numUpdateExprs:", numUpdateExprs);

    // This value should be a function.
    evalLog("lExpr:", lExpr);
    let lExprVal = evalExpr(lExpr, ctx);
    evalLog("lexprval:", lExprVal);
    // assert(lExprVal.type === "function");

    let origFnVal = lExprVal[0]["val"];
    evalLog("fnVal:", origFnVal);
    // Functions, tuples, and records are all considered as functions.
    assert(origFnVal instanceof FcnRcdValue || origFnVal instanceof TupleValue);

    var wasTuple = false;
    // Convert tuple to function for evaluation.
    if (origFnVal instanceof TupleValue) {
        wasTuple = true;
        origFnVal = origFnVal.toFcnRcd();
    }

    evalLog(updateExprs);

    // General form of EXCEPT update expression:
    // [a EXCEPT !.a.b["c"] = "b", ![2].x = 5]
    let updatedFnVal = origFnVal;
    evalLog("origFnVal:", origFnVal);
    for (const updateExpr of updateExprs) {
        evalLog("UPDATE EXPR:", updateExpr);
        let updateSpec = updateExpr.namedChildren[0];
        let newVal = updateExpr.childForFieldName("new_val");

        // Handle each update specifier appropriately e.g.
        // !.a.b["c"]
        evalLog("UPDATE SPEC", updateSpec);
        let updateSpecVals = updateSpec.namedChildren.map(c => {
            if (c.type === "except_update_record_field") {
                // Retrieve field from original function/record value.
                evalLog(c);
                evalLog(origFnVal);
                evalLog(c.namedChildren[0].text);
                return new StringValue(c.namedChildren[0].text);
            } else if (c.type === "except_update_fn_appl") {
                evalLog("except_update_fn_appl", c);
                return evalExpr(c.namedChildren[0], ctx)[0]["val"];
            }
        });

        evalLog("updateSpecVals:", updateSpecVals);

        let newCtx = ctx.clone();
        pathArg = updateSpecVals;
        newCtx.prev_func_val = origFnVal.applyPathArg(pathArg);
        evalLog("new ctx:", newCtx);
        let newRhsVal = evalExpr(newVal, newCtx)[0]["val"];
        // evalLog("updating with path arg:", updateSpecVals);
        updatedFnVal = updatedFnVal.updateWithPath(updateSpecVals, newRhsVal);
    }

    evalLog("updatedFnVal:", updatedFnVal);

    // If the original value was a tuple, then treat this it as a tuple upon return.
    if (wasTuple) {
        updatedFnVal = new TupleValue(updatedFnVal.getValues());
    }

    return [ctx.withVal(updatedFnVal)];
}

function evalSetFilter(ctx, node){
    // Extract the left and right side of the ":" of the set filter.
    let singleQuantBound = node.namedChildren[0];
    let rhsFilter = node.namedChildren[1];

    // Evaluate the quantified domain.
    assert(singleQuantBound.type === "quantifier_bound");
    evalLog("singleQuantBound:", singleQuantBound, singleQuantBound.text);

    // Handle tuple of identifiers case i.e.
    // like {<<a, b>> \in {1,2} \X {3,4} : a + b > 2}
    let tupIdents = null;
    let ident = null;
    if(singleQuantBound.namedChildren[0].type === "tuple_of_identifiers"){
        tupIdents = singleQuantBound.namedChildren[0].namedChildren.filter(c => c.type === "identifier").map(c => c.text);
    } else{
        // Single identifier case.
        ident = singleQuantBound.namedChildren[0].text;
  
    }

    let domainExpr = singleQuantBound.namedChildren[2];
    evalLog(domainExpr);
    let domainExprVal = evalExpr(domainExpr, ctx)[0]["val"];

    evalLog("domainExprVal:", domainExprVal);

    // Return all values in domain for which the set filter evaluates to true.
    let filteredVals = domainExprVal.getElems().filter(exprVal => {
        // Evaluate rhs in context of the bound value and check its truth value.
        let boundContext = ctx.clone();
        if (!boundContext.hasOwnProperty("quant_bound")) {
            boundContext["quant_bound"] = {};
        }

        // Bound each identifier within the tuple if neeeded.
        if (tupIdents) {
            for (var i = 0; i < tupIdents.length; i++) {
                boundContext["quant_bound"][tupIdents[i]] = exprVal.getValues()[i];
            }
        }
        else {
            boundContext["quant_bound"][ident] = exprVal;
        }
        let rhsFilterVal = evalExpr(rhsFilter, boundContext)[0]["val"];
        evalLog("rhsFilterVal:", rhsFilterVal);
        return rhsFilterVal.getVal();
    });
    evalLog("domainExprVal filtered:", filteredVals);
    return [ctx.withVal(new SetValue(filteredVals))];
}

// For debugging.
// TODO: Eventually move this all inside a dedicated class.
let currEvalNode = null;

/**
 * Evaluate a TLC expression for generating initial/next states.
 * 
 * In the simplest case, expression evaluation simply takes in an expression and
 * returns a TLA value. When we are evaluating an expression in the form of an
 * initial state or next state predicate, however, things are more involved. 
 * 
 * That is, when evaluating an initial/next state predicate for generating
 * states, evaluation returns both a boolean value (TRUE/FALSE) as well as an
 * assignment of values to variables. For example, in the context of initial
 * state generation, this is an assignment of values to all variables x1,...,xn
 * declared in a specification. In the context of next state generation, this is
 * an assignment of values to all variables x1,...,xn,x1',...,xn' i.e. the
 * "current" state variables and the "next"/"primed" copy of the state
 * variables. 
 * 
 * Additionally, when generating states during this type of evaluation, we may
 * produce not only a single return value, but a set of return values. That is,
 * we may have one return value for each potential "branch" of the evaluation,
 * corresponding to possible disjunctions that appear in a predicate. For
 * example, the initial state predicate x = 0 \/ x = 1 will produce two possible
 * return values, both of which evaluate to TRUE and which assign the values of
 * 0 and 1, respectively, to the variable 'x'.
 * 
 * To handle this type of evaluation strategy, we allow expression evaluation to
 * take in a current 'Context' object, which consists of several items for
 * tracking data needed during evaluation. See the fields of the 'Context' class
 * definition for an explanation of what data is tracked during expression
 * evaluation.
 * 
 * Expression evaluation can return a list of these context objects, one for
 * each potential evaluation branch of a given expression. Each returned context
 * can contain an assignment of values to variables along with a return value
 * for that expression.
 *
 * In our implementation, we have each evaluation handler function (i.e.
 * 'eval<NAME>') take in a single context object, and return potentially many
 * contexts. This makes it easier to implement each evaluation handler function,
 * by focusing just on how to evaluate an expression given a single context, and
 * either update it, or fork it into multiple new sub-contexts. From this
 * perspective, we can think about the overall evaluation computation as a tree,
 * where each evaluation function takes in a single branch of the tree, and may
 * potentially create several new forks in the tree, corresponding to separate
 * evaluation sub-branches. When the overall computation terminates, each leaf
 * of the tree should represent the result of one evaluation branch, which will
 * contain both a return value for the expression and a potential assignment of
 * values to variables.
 * 
 * @param {TLASyntaxNode} node: TLA+ tree sitter syntax node representing the expression to evaluate.
 * @param {Context} ctx: a 'Context' instance under which to evaluate the given expression.
 * @returns 
 */
function evalExpr(node, ctx) {
    assert(ctx instanceof Context, "Second argument to 'evalExpr' must be of type 'Context'.");

    // Record for debugging purposes.
    currEvalNode = node;

    // evalLog("$$ evalExpr, node: ", node);
    evalLog("evalExpr -> (" + node.type + ") '" + node.text + "'", ctx, ctx.defns_curr_context);

    if(node instanceof LazyValue){
        console.log("Evaluating lazy value.", node);
        return evalExpr(node.expr, node.context);
    }

    if (node.type === "parentheses") {
        return evalExpr(node.namedChildren[0], ctx);
    }

    if (node.type === "let_in") {
        evalLog("LETIN node, ctx:", ctx);
        return evalLetIn(node, ctx);
    }

    if (node.type === "prev_func_val") {
        evalLog(ctx);
        assert(ctx.prev_func_val !== null);
        evalLog("eval prev func");
        return [ctx.withVal(ctx.prev_func_val)];
    }


    if (node.type === "choose") {
        return evalChoose(node, ctx);
    }

    // [<lExpr> EXCEPT ![<updateExpr>] = <rExpr>]
    if (node.type === "except") {
        return evalExcept(node, ctx);
    }

    // <fnVal>[<fnArgVal>] e.g. 'f[3]'
    if (node.type === "function_evaluation") {
        evalLog("function_evaluation: ", node.text);

        let fnVal = null;
        let fnArgVal;

        // Multi-argument function evaluation, treated as tuple argument.
        if (node.namedChildren.length > 2) {
            let argVals = node.namedChildren.slice(1).map(c => evalExpr(c, ctx)[0]["val"]);
            fnArgVal = new TupleValue(argVals);
        } else {
            // Single argument function evaluation.
            fnArgVal = evalExpr(node.namedChildren[1], ctx)[0]["val"];
        }

        // If this is a recursive function evaluation, then we don't want to necessarily evaluate the 
        // values of the function for all domain values upfront. Rather, we can just dynamically evaluate them as
        // we go, starting with the current argument for this function.
        let fnNode = node.namedChildren[0];
        evalLog("fneval (fnval): ", fnArgVal);


        if (fnNode.type === "identifier_ref" &&
            ctx["defns_curr_context"] !== undefined &&
            ctx["defns_curr_context"].map(defid => ctx.global_def_table[defid].name).includes(fnNode.text) &&
            _.find(ctx.global_def_table, o => o.name === fnNode.text && ctx["defns_curr_context"].includes(o.id))["node"].type === "function_definition"
        ) {

            // If this function has been previously defined, we need to look up its definition.
            evalLog("EVAL function def defns_curr_context:", ctx["defns_curr_context"]);

            // Look up the def in the global module table.
            let fnDef = ctx.getDefnInCurrContext(fnNode.text)

            let fnExpr = _.last(fnDef.node.namedChildren);
            let quant_bounds = fnDef["quant_bounds"];
            // console.log("[fndefeval] fnDefNode:", fnDefNode);
            // console.log("[fndefeval] quant_bounds:", quant_bounds);
            // console.log("[fndefeval] fnArgVal:", fnArgVal);
            ret = evalFunctionLiteralInner(ctx, quant_bounds, fnExpr, fnArgVal);
            let fnVal = ret[0]["val"];
            let res = fnVal.applyArg(fnArgVal);
            // console.log("fres:", res);
            return [ctx.withVal(res)];
        }

        // Otherwise proceed to evaluate function normally.
        evalLog("fneval (fnval,fnarg): ", fnVal, ",", fnArgVal);
        fnVal = evalExpr(node.namedChildren[0], ctx)[0]["val"];

        // Tuples are considered as functions with natural number domains.
        let fnValRes;
        if (fnVal instanceof TupleValue) {
            evalLog("applying tuple as function", fnVal);
            assert(fnArgVal instanceof IntValue);
            let index = fnArgVal.getVal();
            // Account for 1-indexing.
            fnValRes = fnVal.getElems()[index - 1];
        } else {
            fnValRes = fnVal.applyArg(fnArgVal);
        }
        evalLog("fnValRes:", fnValRes);
        return [ctx.withVal(fnValRes)];
    }

    if (isPrimedVar(node, ctx)) {
        // See if this variable is already assigned a value in the current context, and if so, return it.
        if (ctx.state.getVarVal(node.text) !== null) {
            return [ctx.withVal(ctx.state.getVarVal(node.text))];
        }
    }


    if (node.type === "comment") {
        // TOOD: Handle properly.
    }

    // Do some comment cleanup as necessary.
    _.remove(node.children, isCommentNode);
    _.remove(node.namedChildren, isCommentNode);


    if (node === undefined) {
        return [ctx.withVal(false)];
    }
    if (node.type === "conj_list") {
        let ret = evalConjList(node, node.children, ctx);
        evalLog("evalConjList ret: ", ret);
        return ret;
    }
    if (node.type === "disj_list") {
        return evalDisjList(node, node.children, ctx);
    }
    if (node.type === "conj_item") {
        conj_item_node = node.children[1];
        return evalExpr(conj_item_node, ctx);
    }
    if (node.type === "disj_item") {
        disj_item_node = node.children[1];
        return evalExpr(disj_item_node, ctx);
    }

    if (node.type === "bound_op") {
        return evalBoundOp(node, ctx)
    }

    if (node.type === "prefixed_op") {
        return evalPrefixedOp(node, ctx);
    }

    if (node.type === "bound_infix_op") {
        // evalLog(node.type + ", ", node.text, ", ctx:", JSON.stringify(contexts));
        return evalBoundInfix(node, ctx);
    }

    if (node.type === "bound_prefix_op") {
        return evalBoundPrefix(node, ctx);
    }

    if (node.type === "bound_postfix_op") {
        return evalBoundPostfix(node, ctx);
    }

    // TODO: Finish this after implementing 'except' node type handling.
    if (node.type === "bounded_quantification") {
        return evalBoundedQuantification(node, ctx);
    }

    if (node.type === "identifier_ref") {
        return evalIdentifierRef(node, ctx);
    }

    if (node.type === "if_then_else") {
        let cond = node.childForFieldName("if");
        let thenNode = node.childForFieldName("then");
        let elseNode = node.childForFieldName("else");

        let condVal = evalExpr(cond, ctx.clone())[0]["val"];
        if (condVal.getVal()) {
            let thenVal = evalExpr(thenNode, ctx.clone());
            evalLog("thenVal", thenVal, thenNode.text);
            return thenVal;
        } else {
            let elseVal = evalExpr(elseNode, ctx.clone());
            evalLog("elseVal", elseVal, elseNode.text, ctx);
            return elseVal;
        }
    }

    // CASE statement.
    if (node.type === "case") {
        let caseArms = node.namedChildren.filter(n => n.type === "case_arm");
        let otherArms = node.namedChildren.filter(n => n.type === "other_arm");
        for (var caseArm of caseArms) {
            let cond = caseArm.namedChildren[0];
            let out = caseArm.namedChildren[2];
            let condVal = evalExpr(cond, ctx)[0]["val"];
            evalLog("condVal: ", condVal);
            // Short-circuit on the first true condition out of the CASE branches.
            if (condVal.getVal()) {
                return evalExpr(out, ctx);
            }
        }

        // If we get here, it means none of the case arm conditions evaluated to
        // true, so we now check for an OTHER arm. If none exists, throw an
        // error.
        if (otherArms.length === 0) {
            throw new Error("No CASE condition was TRUE.")
        } else {
            let out = otherArms[0].namedChildren[1];
            evalLog("Evaluating OTHER case arm.", out);
            return evalExpr(out, ctx);
        }
    }

    // [<D_expr> -> <R_expr>]
    // e.g. [{"x","y"} -> {1,2}]
    if (node.type === "set_of_functions") {
        return evalSetOfFunctions(node, ctx);
    }

    // [<fieldname> : <D_expr>, ..., <fieldnameN> : <D_exprN>]
    // e.g. [a : {1,2}, b : {3,4}]
    if (node.type === "set_of_records") {
        return evalSetOfRecords(node, ctx);
    }

    //
    // {<bound_expr> : <setin_expr>}
    // e.g. 
    // { x+2 : x \in {1,2,3}}
    // {<<a, b>> : a \in 1..3, b \in 1..3}
    //
    // In general, set maps can look like:
    // {<expr> : a,b \in S1, c \in S2}
    //
    if (node.type === "set_map") {
        evalLog("SET_MAP");
        let lhsExpr = node.namedChildren[0];
        let rightQuantBounds = node.namedChildren.filter(n => n.type === "quantifier_bound");

        // Extract set of quantified variables and their domains.
        let identsAndDomains = rightQuantBounds.map(qb => {
            evalLog("qb:", qb);
            let qDomain = evalExpr(_.last(qb.namedChildren), ctx)[0]["val"];
            return qb.namedChildren
                .filter(n => n.type === "identifier" || n.type === "tuple_of_identifiers")
                .map(n => {
                    // In this case the domain should be a set of tuples, where each 
                    // element gets bound to the associated identifier in the tuple of
                    // identifiers e.g.
                    // { a+b : <<a,b>> \in {<<1,2>>, <<3,4>>}}
                    if (n.type === "tuple_of_identifiers") {
                        let tupIdentNames = n.namedChildren.filter(c => c.type === "identifier").map(c => c.text);
                        return [tupIdentNames, qDomain]
                    } else {
                        return [n.text, qDomain]
                    }
                });
        });

        identsAndDomains = _.flatten(identsAndDomains);
        evalLog("identsAndDomains", identsAndDomains)

        let idents = _.unzip(identsAndDomains)[0];
        let domains = _.unzip(identsAndDomains)[1].map(v => v.getElems());
        evalLog("domains:", domains);

        let domainProd = cartesianProductOf(...domains);
        evalLog("domainProd:", domainProd);

        let retVal = domainProd.map((tup) => {
            evalLog("tup: ", tup);
            let boundContext = ctx.clone();
            if (!boundContext.hasOwnProperty("quant_bound")) {
                boundContext["quant_bound"] = {};
            }
            var ind = 0;
            for (var name of idents) {
                if (name instanceof Array) {
                    let names = name;
                    console.log("array tup idents:", names);
                    for (var subind = 0; subind < names.length; subind++) {
                        boundContext["quant_bound"][names[subind]] = tup[ind].getElems()[subind];
                    }
                } else {
                    boundContext["quant_bound"][name] = tup[ind];
                }
                ind += 1;
            }
            return evalExpr(lhsExpr, boundContext)[0]["val"];
        })
        return [ctx.withVal(new SetValue(retVal))];
    }

    // {<single_quantifier_bound> : <expr>}
    // {i \in A : <expr>}
    if (node.type === "set_filter") {
        evalLog("SET_FILTER", node);
        return evalSetFilter(ctx, node);
    }

    // <record>.<field>
    if (node.type === "record_value") {
        evalLog("RECVAL", node);
        let rec = node.namedChildren[0];
        let recField = node.namedChildren[1].text;

        let recVal = evalExpr(rec, ctx)[0]["val"];
        evalLog("recVal", recVal);
        evalLog("recField", recField);
        let fieldVal = recVal.applyArg(new StringValue(recField));
        return [ctx.withVal(fieldVal)];
    }

    //
    // Evaluation of some built-in constants.
    //

    // The 'BOOLEAN' built-in constant representing the set of all boolean values.
    if (node.type === "boolean_set") {
        // console.log(node.type, node.text);
        let boolSet = [new BoolValue(true), new BoolValue(false)];
        return [ctx.withVal(new SetValue(boolSet))];
    }


    //
    // Evaluation of raw literal values.
    //

    if (node.type === "nat_number") {
        // console.log(node.type, node.text);
        // ctx.eval_node = {"children": [parseInt(node.text)]}
        ctx.eval_node = new AbstractEvalNode("nat_number_" + node.text, "nat_number", [parseInt(node.text)]);
        return [ctx.withVal(new IntValue(parseInt(node.text)))];
    }

    if (node.type === "boolean") {
        evalLog(node.type, node.text);
        let boolVal = node.text === "TRUE" ? true : false;
        return [ctx.withVal(new BoolValue(boolVal))];
    }

    if (node.type === "string") {
        evalLog("string node", node.text);
        // Remove the quotes.
        let rawStr = node.text.substring(1, node.text.length - 1);
        return [ctx.withVal(new StringValue(rawStr))];
    }

    // TODO: Re-examine whether this implementation is correct.
    if (node.type === "finite_set_literal") {
        return evalFiniteSetLiteral(node, ctx);
    }

    // <<e1,e2,...,en>>
    if (node.type === "tuple_literal") {
        evalLog("tuple_literal", node);
        let elems = node.namedChildren.slice(1, node.namedChildren.length - 1);

        tupleVals = elems.map(el => evalExpr(el, ctx)[0]["val"]);
        return [ctx.withVal(new TupleValue(tupleVals))];
    }

    // [<identifier> |-> <expr>, <identifier> |-> <expr>, ...]
    // "|->" is of type 'all_map_to'.
    if (node.type === "record_literal") {
        evalLog("RECLIT", node);
        let record_obj = {};
        let recordDom = [];
        let recordVals = [];
        let namedChildrenVals = node.namedChildren.filter(isNotCommentNode);
        for (var i = 0; i < namedChildrenVals.length; i += 3) {
            let ident = namedChildrenVals[i]
            let exprNode = namedChildrenVals[i + 2]

            let identName = ident.text;
            let exprVal = evalExpr(exprNode, ctx);
            record_obj[identName] = exprVal[0]["val"];
            recordDom.push(new StringValue(identName));
            recordVals.push(exprVal[0]["val"]);
        }
        let isRecord = true;
        let recVal = new FcnRcdValue(recordDom, recordVals, isRecord);
        evalLog("RECOBJ", recVal);
        return [ctx.withVal(recVal)];
    }


    // "[" <quantifier_bound> "|->" <expr> "]"
    if (node.type === "function_literal") {
        return evalFunctionLiteral(node, ctx);
    }
}

/**
 * Generates all possible initial states given the syntax tree node for the
 * initial state predicate and an object 'vars' which contains exactly the
 * specification's state variables as keys.
 */
function getInitStates(initDef, vars, defns, constvals, moduleTable, globalDefTable, spec, initDefName="Init", defOverrides={}) {
    // TODO: Pass this variable value as an argument to the evaluation functions.
    ASSIGN_PRIMED = false;
    depth = 0;

    // Values of each state variable. Initially empty.
    init_var_vals = {};
    for (v in vars) {
        init_var_vals[v] = null;
    }
    let emptyInitState = new TLAState(init_var_vals);

    // We refer to a 'context' as the context for a single evaluation
    // branch, which contains a computed value along with a list of 
    // generated states.
    let initCtx = new Context(null, emptyInitState, defns, {}, constvals, null, null, moduleTable);
    initCtx.setGlobalDefTable(_.cloneDeep(globalDefTable));
    initCtx.setSpecObj(spec);
    initCtx.setDefOverrides(defOverrides);
    initCtx["defns_curr_context"] = spec.getDefinitionByName(initDefName)["curr_defs_context"];

    let ret_ctxs = evalExpr(initDef, initCtx);
    if (ret_ctxs === undefined) {
        console.error("Set of generated initial states is 'undefined'.");
    }
    return ret_ctxs;
}

/**
 * Generates all possible successor states from a given state and the syntax
 * tree node for the definition of the next state predicate.
 */
function getNextStates(nextDef, currStateVars, defns, constvals, moduleTable, globalDefTable, spec, nextDefName="Next", defOverrides={}) {
    // TODO: Pass this variable value as an argument to the evaluation functions.
    ASSIGN_PRIMED = true;
    depth = 0;
    let origVars = Object.keys(currStateVars.stateVars);

    for (var k in currStateVars.stateVars) {
        let primedVar = k + "'";
        currStateVars.stateVars[primedVar] = null;
    }
    evalLog("currStateVars:", currStateVars);

    let initCtx = new Context(null, currStateVars, defns, {}, constvals, null, null, moduleTable);
    initCtx.setGlobalDefTable(_.cloneDeep(globalDefTable));
    initCtx.setSpecObj(spec);
    initCtx.setDefOverrides(defOverrides);
    initCtx["defns_curr_context"] = spec.getDefinitionByName(nextDefName)["curr_defs_context"];
    // console.log("currStateVars:", currStateVars);
    let ret = evalExpr(nextDef, initCtx);
    evalLog("getNextStates eval ret:", ret);

    // Filter out disabled transitions.
    ret = ret.filter(c => c["val"].getVal() === true);

    evalLog("getNextStates without disabled transitions:", ret);

    // Filter out transitions that do not modify the state.
    // let all_next_states = ret.filter(c => {
    //     return !_.every(origVars, (v) => c.state.getVarVal(v).fingerprint() === c.state.getVarVal(v+"'").fingerprint());
    // });

    // Only keep states where all primed variables were assigned.
    let all_next_states = ret.filter(c => _.every(origVars, v => c.state.getVarVal(v + "'") !== null));
    let next_states_with_unassigned = ret.filter(c => _.some(origVars, v => c.state.getVarVal(v + "'") === null));

    // If there are some states with unassigned variables, throw an error and print out some info about which
    // variables are unassigned.
    if (next_states_with_unassigned.length !== 0) {
        console.log("next_states_with_unassigned:", next_states_with_unassigned);
        for (const state of next_states_with_unassigned) {
            console.log("STATE:");
            for (const v of origVars) {
                if (state["state"].getVarVal(v + "'") === null) {
                    console.log("state with unassigned variable:", v + "'");
                }
            }
        }
        throw new Error(`${next_states_with_unassigned.length} generated next states had unassigned variables.`);
    }


    // Filter to set of distinct generated states.
    all_next_states = _.uniqBy(all_next_states, c => c.state.fingerprint());

    // TODO: Check if we are correctly keeping only unique states.
    // all_next_states = _.uniqBy(all_next_states, c => c.state.fingerprint());

    // Keep only unique states, based on hashed fingerprint value.
    evalLog("getNextStates all:", all_next_states);
    return all_next_states;
}

class TlaInterpreter {

    computeInitStates(treeObjs, constvals, includeFullCtx, spec, initDefName=null, defOverrides={}) {
        var includeFullCtx = includeFullCtx || false;

        var initDefName = initDefName || "Init";

        let consts = treeObjs["const_decls"];
        let vars = treeObjs["var_decls"];
        let defns = treeObjs["op_defs"];

        // Reset for debugging.
        evalNodeGraph = [];
        edgeOrder = 0;

        evalNodeError = [];

        evalLog("consts:", consts);

        let initDef = spec.getDefinitionByName(initDefName);
        evalLog("initDef.childCount: ", initDef["node"].childCount);
        evalLog("initDef.type: ", initDef["node"].type);

        let initStates = getInitStates(initDef["node"], vars, defns, constvals, treeObjs["module_table"], spec.globalDefTable, spec, initDefName, defOverrides);
        // Keep only the valid states.
        if(includeFullCtx){
            return initStates.filter(actx => actx["val"].getVal())
        } else{
            return initStates.filter(actx => actx["val"].getVal()).map(actx => actx["state"]);
        }
    }

    computeNextStates(treeObjs, constvals, initStates, action, spec, nextDefName, defOverrides={}) {
        let consts = treeObjs["const_decls"];
        let vars = treeObjs["var_decls"];
        let defns = treeObjs["op_defs"];

        var nextDefName = nextDefName || "Next";

        // Reset for debugging.
        evalNodeGraph = [];
        edgeOrder = 0;

        evalNodeError = [];

        let nextDef = spec.getDefinitionByName(nextDefName)["node"];

        // Optionally specify an action to consider as the next state relation
        // when computing next state.
        if (action) {
            nextDef = action;
        }
        // console.log(defns);
        // console.log("<<<< NEXT >>>>");       

        let allNext = [];
        for (const istate of initStates) {
            let currState = _.cloneDeep(istate);
            // console.log("###### Computing next states from state: ", currState);
            let ret = getNextStates(nextDef, currState, defns, constvals, treeObjs["module_table"], spec.globalDefTable, spec, nextDefName, defOverrides);
            allNext = allNext.concat(ret);
        }
        return allNext;
    }

    /**
     * Compute all reachable states for the given spec and its instantiated
     * constant values. If 'checkInvExpr' is given, check if this invariant
     * holds in each state, and terminate upon encountering the first violation.
     */
    computeReachableStates(treeObjs, constvals, checkInvExpr, spec, logMetricsInterval=null) {
        // console.log("TREEOBJS:", treeObjs);
        // console.log("TREEOBJS:", spec.globalDefTable);
        let vars = treeObjs["var_decls"];
        let defns = treeObjs["op_defs"];

        let initDef = defns["Init"];
        let nextDef = defns["Next"];

        // Compute initial states and keep only the valid ones.
        // let initStates = getInitStates(initDef["node"], vars, defns, constvals);
        // console.log("[INIT] Computing initial states");
        let initStates = this.computeInitStates(treeObjs, constvals, undefined, spec);

        let initStatesOrig = _.cloneDeep(initStates);
        let initStatesOrigFingerprints = initStatesOrig.map(s => s.fingerprint());
        // console.log("initStatesOrig:", initStatesOrig.map(s => s.fingerprint()));
        let stateQueue = initStates;
        let seenStatesHashSet = new Set();
        let reachableStates = [];
        let edges = [];
        let statePredecessorMap = {};
        while (stateQueue.length > 0) {
            // console.log("initStatesOrig:", initStatesOrig);
            let currState = stateQueue.shift();
            // console.log(currState);
            let currStateHash = currState.fingerprint();
            // console.log("curr state hash:", currStateHash);

            // If we've already seen this state, we don't need to explore it.
            if (seenStatesHashSet.has(currStateHash)) {
                // console.log("already seen state " + currStateHash);
                continue;
            }

            // Mark the state as seen and record it as reachable.
            seenStatesHashSet.add(currStateHash);
            reachableStates.push(currState);

            // For online reporting of metrics.
            if(logMetricsInterval !== null && seenStatesHashSet.size % logMetricsInterval === 0){
                console.log(`${seenStatesHashSet.size} reachable states computed.`);
            }

            // Compute next states reachable from the current state, and add
            // them to the state queue.
            let currStateArg = _.cloneDeep(currState);
            let nextStateCtxs = this.computeNextStates(treeObjs, constvals, [currStateArg], undefined, spec)
            let nextStates = nextStateCtxs.map(c => c["state"].deprimeVars());
            // console.log("nextStates:", nextStates);
            // console.log("reachableStates:", reachableStates);
            stateQueue = stateQueue.concat(nextStates);
            for (const nextSt of nextStates) {
                edges.push([currStateArg, nextSt]);

                // If we have already visited this state, we don't need to record path to it.
                if(!statePredecessorMap.hasOwnProperty(nextSt.fingerprint())){
                    statePredecessorMap[nextSt.fingerprint()] = currStateHash;
                }
            }

            // Check invariant in next states.
            if (checkInvExpr !== undefined) {
                for (const nextState of nextStates) {
                    let consts = treeObjs["const_decls"];
                    let vars = treeObjs["var_decls"];
                    let defns = treeObjs["op_defs"];
                    let ctx = new Context(null, nextState, defns, {}, constvals);


                    // All definitions in the root module should be accessible.
                    ctx["defns_curr_context"] = _.keys(spec.spec_obj["op_defs"]);
                    ctx.setGlobalDefTable(spec.globalDefTable);
                    ctx.setSpecObj(spec);

                    let res = evalExprStrInContext(ctx, checkInvExpr);
                    // console.log("invariant check: ", res);
                    // Invariant failed to hold in this state.
                    if (!res.getVal()) {
                        console.log("Invariant violated: ", res, nextState);

                        // Reconstruct trace.
                        console.log("Reconstructing trace from predecessor map:", statePredecessorMap);
                        let currTraceState = nextState;
                        let currTraceStateHash = currTraceState.fingerprint();
                        let trace = [currTraceStateHash];
                        console.log("invariant violated in state:", currTraceStateHash);

                        while (statePredecessorMap.hasOwnProperty(currTraceStateHash) && !initStatesOrigFingerprints.includes(currTraceStateHash)) {
                            // console.log("currTraceStateHash:", currTraceStateHash);
                            let nextTraceStateHash = statePredecessorMap[currTraceStateHash];
                            trace.push(nextTraceStateHash);
                            currTraceStateHash = nextTraceStateHash;
                        }
                        // Trace starts from an initial state.
                        trace = _.reverse(trace);

                        return {
                            "initStates": initStatesOrig,
                            "states": [],
                            "edges": [],
                            "invHolds": false,
                            "invFirstViolatingState": nextState,
                            "hashTrace": trace,
                            "numStatesExplored": seenStatesHashSet.size
                        }
                    }
                }
            }

        }
        return {
            "initStates": initStatesOrig,
            "states": reachableStates,
            "numStatesExplored": seenStatesHashSet.size,
            "edges": edges,
            "invHolds": true
        }
    }
}

//
// For debugging/tracing expression evaluation.
//

let parent = null;
let parentCtx = null;
let evalNodeGraph = [];
let edgeOrder = 0;

let origevalExpr = evalExpr;
let evalNodeError = [];
evalExpr = function (...args) {
    if(!enableEvalTracing){
        // If an exception is thrown, capture the node throwing the exception.
        let ret;
        try{
            ret = origevalExpr(...args);
        } catch (e) {
            evalNodeError.push(args[0]);
            throw e;
        }
        return ret;
    }
    depth += 1;

    // let ctx = args[1];
    // let currAssignedVars = _.keys(ctx["state"].vars).filter(k => ctx["state"].vars[k] !== null)
    // evalLog("curr assigned vars:", currAssignedVars);

    // Test out tracking of evaluation graph for debugging.
    let currNode = args[0];
    let currCtx = args[1];

    function boundCtxStr(ctxArg) {
        let boundVals = _.toPairs(ctxArg.quant_bound);
        boundVals = _.sortBy(boundVals, p => p[0]);
        let boundValsStr = boundVals.map(p => p[0] + "<-" + p[1].toString()).join("_");
        if (boundValsStr.length === 0) {
            return ""
        }
        return "_$$$_" + boundValsStr;
    }

    // Also should consider the values in the context as part of the node's 
    // identity in the eval graph.
    let boundValsStr = boundCtxStr(currCtx);

    let edge = null;
    let nodeText = currNode.text + boundValsStr;
    if (parent !== null) {
        let parentNodeText = parent.text + boundCtxStr(parentCtx);
        // console.log("nodeedge:", "\"" + currNode.text + "\"", "->", "\"" + parent.text + "\"");
        edge = [{textId:nodeText, type:currNode.type}, {textId:parentNodeText, type:parent.type}]
        // evalNodeGraph.push([currNode.text, parent.text]);
    }

    let origParent = parent;
    let origParentCtx = parentCtx;
    parent = args[0];
    parentCtx = args[1];

    let start = performance.now();

    // Run the original function to evaluate the expression.
    let ret = origevalExpr(...args);
    const duration = (performance.now() - start).toFixed(1);

    evalLog("evalreturn -> ", ret, args[0].text);
    parent = origParent;
    parentCtx = origParentCtx;

    if (edge !== null && enableEvalTracing) {
        evalNodeGraph.push([edge, ret, edgeOrder, duration]);
        edgeOrder += 1;
    }

    // evalLog("num ret ctxs: " , ret.length);
    // evalLog("evalreturn num ctxs: ", ret.length);

    // evalLog("evalreturn num ctxs: ", ret.length);

    // Evaluation DOT graph printing.
    if (enableEvalTracing) {
        // let Gstr = evalNodeGraph.map(e => "\"" + e[0] + "\"" + " -> " + "\"" + e[1] + "\"").join(";") + ";";
        // console.log(Gstr.replaceAll("\\", "\\\\"));
    }

    depth -= 1;
    return ret;
}

let origevalBoundInfix = evalBoundInfix;
evalBoundInfix = function (...args) {
    depth += 1;
    let ret = origevalBoundInfix(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}

let origevalConjList = evalConjList;
evalConjList = function (...args) {
    depth += 1;
    let ret = origevalConjList(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}
    