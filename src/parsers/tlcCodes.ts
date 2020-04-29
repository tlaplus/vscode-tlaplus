// TLC message constants
// https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/output/EC.java
// Commit ab14a33

export enum TlcCodeType {
    Info,       // Such messages must be processed by the parser somehow
    Warning,    // Such messages will be converted into warnings (not supported at the moment)
    Error,      // Such messages will be converted into errors
    Ignore      // Such messages will be ignored by the parser
}

export class TlcCode {
    constructor(
        readonly num: number,
        readonly type: TlcCodeType
    ) {}
}

const TLC_CODES = new Map<number, TlcCode>();

export function getTlcCode(num: number): TlcCode | undefined {
    return TLC_CODES.get(num);
}

export const NO_ERROR = registerCode(0, TlcCodeType.Ignore);

// Check and CheckImpl
// check if the TLC option is the same for params
export const CHECK_FAILED_TO_CHECK = registerCode(3000, TlcCodeType.Error);
export const CHECK_COULD_NOT_READ_TRACE = registerCode(3001, TlcCodeType.Error);

export const CHECK_PARAM_EXPECT_CONFIG_FILENAME = registerCode(3100, TlcCodeType.Error);
export const CHECK_PARAM_USAGE = registerCode(3101, TlcCodeType.Error);
export const CHECK_PARAM_MISSING_TLA_MODULE = registerCode(3102, TlcCodeType.Error);
export const CHECK_PARAM_NEED_TO_SPECIFY_CONFIG_DIR = registerCode(3103, TlcCodeType.Error);
export const CHECK_PARAM_WORKER_NUMBER_REQUIRED = registerCode(3104, TlcCodeType.Error);
export const CHECK_PARAM_WORKER_NUMBER_TOO_SMALL = registerCode(3105, TlcCodeType.Error);
export const CHECK_PARAM_WORKER_NUMBER_REQUIRED2 = registerCode(3106, TlcCodeType.Error);
export const CHECK_PARAM_DEPTH_REQUIRED = registerCode(3107, TlcCodeType.Error);
export const CHECK_PARAM_DEPTH_REQUIRED2 = registerCode(3108, TlcCodeType.Error);
export const CHECK_PARAM_TRACE_REQUIRED = registerCode(3109, TlcCodeType.Error);
export const CHECK_PARAM_COVREAGE_REQUIRED = registerCode(3110, TlcCodeType.Error);
export const CHECK_PARAM_COVREAGE_REQUIRED2 = registerCode(3111, TlcCodeType.Error);
export const CHECK_PARAM_COVREAGE_TOO_SMALL = registerCode(3112, TlcCodeType.Error);
export const CHECK_PARAM_UNRECOGNIZED = registerCode(3113, TlcCodeType.Error);
export const CHECK_PARAM_TOO_MANY_INPUT_FILES = registerCode(3114, TlcCodeType.Error);

export const SANY_PARSER_CHECK_1 = registerCode(4000, TlcCodeType.Ignore);
export const SANY_PARSER_CHECK_2 = registerCode(4001, TlcCodeType.Error);
export const SANY_PARSER_CHECK_3 = registerCode(4002, TlcCodeType.Error);

export const UNIT_TEST = registerCode(-123456, TlcCodeType.Ignore);

export const TLC_FEATURE_UNSUPPORTED = registerCode(2156, TlcCodeType.Error);
export const TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY = registerCode(2279, TlcCodeType.Error);
export const TLC_FEATURE_LIVENESS_CONSTRAINTS = registerCode(2284, TlcCodeType.Warning);

export const GENERAL = registerCode(1000, TlcCodeType.Info);
export const SYSTEM_OUT_OF_MEMORY = registerCode(1001, TlcCodeType.Error);
export const SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT = registerCode(1002, TlcCodeType.Error);
export const SYSTEM_STACK_OVERFLOW = registerCode(1005, TlcCodeType.Error);

export const WRONG_COMMANDLINE_PARAMS_SIMULATOR = registerCode(1101, TlcCodeType.Error);
export const WRONG_COMMANDLINE_PARAMS_TLC = registerCode(1102, TlcCodeType.Error);

export const TLC_PP_PARSING_VALUE = registerCode(2000, TlcCodeType.Error);
export const TLC_PP_FORMATING_VALUE = registerCode(2001, TlcCodeType.Error);

export const TLC_METADIR_EXISTS = registerCode(2100, TlcCodeType.Error);
export const TLC_METADIR_CAN_NOT_BE_CREATED = registerCode(2101, TlcCodeType.Error);
export const TLC_INITIAL_STATE = registerCode(2102, TlcCodeType.Error);
export const TLC_NESTED_EXPRESSION = registerCode(2103, TlcCodeType.Error);
export const TLC_ASSUMPTION_FALSE = registerCode(2104, TlcCodeType.Error);
export const TLC_ASSUMPTION_EVALUATION_ERROR = registerCode(2105, TlcCodeType.Error);
export const TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL = registerCode(2106, TlcCodeType.Error);

export const TLC_INVARIANT_VIOLATED_INITIAL = registerCode(2107, TlcCodeType.Error);
export const TLC_PROPERTY_VIOLATED_INITIAL = registerCode(2108, TlcCodeType.Error);
export const TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT = registerCode(2109, TlcCodeType.Error);
export const TLC_INVARIANT_VIOLATED_BEHAVIOR = registerCode(2110, TlcCodeType.Error);
export const TLC_INVARIANT_EVALUATION_FAILED = registerCode(2111, TlcCodeType.Error);
export const TLC_INVARIANT_VIOLATED_LEVEL = registerCode(2146, TlcCodeType.Error);
export const TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR = registerCode(2112, TlcCodeType.Error);
export const TLC_ACTION_PROPERTY_EVALUATION_FAILED = registerCode(2113, TlcCodeType.Error);
export const TLC_DEADLOCK_REACHED = registerCode(2114, TlcCodeType.Error);

export const TLC_STATES_AND_NO_NEXT_ACTION = registerCode(2115, TlcCodeType.Error);
export const TLC_TEMPORAL_PROPERTY_VIOLATED = registerCode(2116, TlcCodeType.Error);
export const TLC_FAILED_TO_RECOVER_NEXT = registerCode(2117, TlcCodeType.Error);
export const TLC_NO_STATES_SATISFYING_INIT = registerCode(2118, TlcCodeType.Error);
export const TLC_STRING_MODULE_NOT_FOUND = registerCode(2119, TlcCodeType.Error);

export const TLC_ERROR_STATE = registerCode(2120, TlcCodeType.Error);
export const TLC_BEHAVIOR_UP_TO_THIS_POINT = registerCode(2121, TlcCodeType.Ignore);
export const TLC_BACK_TO_STATE = registerCode(2122, TlcCodeType.Info);
export const TLC_FAILED_TO_RECOVER_INIT = registerCode(2123, TlcCodeType.Error);
export const TLC_REPORTER_DIED = registerCode(2124, TlcCodeType.Error);

export const SYSTEM_ERROR_READING_POOL = registerCode(2125, TlcCodeType.Error);
export const SYSTEM_CHECKPOINT_RECOVERY_CORRUPT = registerCode(2126, TlcCodeType.Error);
export const SYSTEM_ERROR_WRITING_POOL = registerCode(2127, TlcCodeType.Error);
export const SYSTEM_ERROR_CLEANING_POOL = registerCode(2270, TlcCodeType.Error);
export const SYSTEM_INDEX_ERROR = registerCode(2134, TlcCodeType.Error);
export const SYSTEM_STREAM_EMPTY = registerCode(2135, TlcCodeType.Error);
export const SYSTEM_FILE_NULL = registerCode(2137, TlcCodeType.Error);
export const SYSTEM_INTERRUPTED = registerCode(2138, TlcCodeType.Error);
export const SYSTEM_UNABLE_NOT_RENAME_FILE = registerCode(2160, TlcCodeType.Error);
export const SYSTEM_DISK_IO_ERROR_FOR_FILE = registerCode(2161, TlcCodeType.Error);
export const SYSTEM_METADIR_EXISTS = registerCode(2162, TlcCodeType.Error);
export const SYSTEM_METADIR_CREATION_ERROR = registerCode(2163, TlcCodeType.Error);
export const SYSTEM_UNABLE_TO_OPEN_FILE = registerCode(2167, TlcCodeType.Error);
export const TLC_BUG = registerCode(2128, TlcCodeType.Error);
export const TLC_FINGERPRINT_EXCEPTION = registerCode(2147, TlcCodeType.Error);

export const SYSTEM_DISKGRAPH_ACCESS = registerCode(2129, TlcCodeType.Error);

export const TLC_AAAAAAA = registerCode(2130, TlcCodeType.Error);
export const TLC_REGISTRY_INIT_ERROR = registerCode(2131, TlcCodeType.Error);
export const TLC_CHOOSE_ARGUMENTS_WRONG = registerCode(2164, TlcCodeType.Error);
export const TLC_CHOOSE_UPPER_BOUND = registerCode(2165, TlcCodeType.Error);

export const TLC_VALUE_ASSERT_FAILED = registerCode(2132, TlcCodeType.Error);
export const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE = registerCode(2154, TlcCodeType.Error);
export const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED = registerCode(2168, TlcCodeType.Ignore);
export const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH = registerCode(2400, TlcCodeType.Error);
export const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH = registerCode(2402, TlcCodeType.Error);
export const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH = registerCode(2403, TlcCodeType.Error);
export const TLC_MODULE_OVERRIDE_STDOUT = registerCode(20000, TlcCodeType.Info);

export const TLC_FP_NOT_IN_SET = registerCode(2133, TlcCodeType.Error);
export const TLC_FP_VALUE_ALREADY_ON_DISK = registerCode(2166, TlcCodeType.Error);

export const TLC_LIVE_BEGRAPH_FAILED_TO_CONSTRUCT = registerCode(2159, TlcCodeType.Error);
export const TLC_PARAMETER_MUST_BE_POSTFIX = registerCode(2136, TlcCodeType.Error);
export const TLC_COULD_NOT_DETERMINE_SUBSCRIPT = registerCode(2139, TlcCodeType.Error);
export const TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR = registerCode(2140, TlcCodeType.Error);
export const TLC_WRONG_TUPLE_FIELD_NAME = registerCode(2141, TlcCodeType.Error);
export const TLC_WRONG_RECORD_FIELD_NAME = registerCode(2142, TlcCodeType.Error);
export const TLC_UNCHANGED_VARIABLE_CHANGED = registerCode(2143, TlcCodeType.Error);
export const TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD = registerCode(2144, TlcCodeType.Error);

export const TLC_MODULE_TLCGET_UNDEFINED = registerCode(2145, TlcCodeType.Error);
export const TLC_MODULE_COMPARE_VALUE = registerCode(2155, TlcCodeType.Error);
export const TLC_MODULE_CHECK_MEMBER_OF = registerCode(2158, TlcCodeType.Error);
export const TLC_MODULE_TRANSITIVE_CLOSURE = registerCode(2157, TlcCodeType.Error);
export const TLC_MODULE_ARGUMENT_ERROR = registerCode(2169, TlcCodeType.Error);
export const TLC_MODULE_ARGUMENT_ERROR_AN = registerCode(2266, TlcCodeType.Error);
export const TLC_MODULE_ONE_ARGUMENT_ERROR = registerCode(2283, TlcCodeType.Error);
export const TLC_ARGUMENT_MISMATCH = registerCode(2170, TlcCodeType.Error);
export const TLC_PARSING_FAILED2 = registerCode(2171, TlcCodeType.Error);
export const TLC_PARSING_FAILED = registerCode(3002, TlcCodeType.Error);
export const TLC_TOO_MNY_POSSIBLE_STATES = registerCode(2172, TlcCodeType.Error);
export const TLC_ERROR_REPLACING_MODULES = registerCode(2173, TlcCodeType.Error);
export const SYSTEM_ERROR_READING_STATES = registerCode(2174, TlcCodeType.Error);
export const SYSTEM_ERROR_WRITING_STATES = registerCode(2175, TlcCodeType.Error);
export const TLC_MODULE_APPLYING_TO_WRONG_VALUE = registerCode(2176, TlcCodeType.Error);
export const TLC_MODULE_BAG_UNION1 = registerCode(2177, TlcCodeType.Error);
export const TLC_MODULE_OVERFLOW = registerCode(2178, TlcCodeType.Error);
export const TLC_MODULE_DIVISION_BY_ZERO = registerCode(2179, TlcCodeType.Error);
export const TLC_MODULE_NULL_POWER_NULL = registerCode(2180, TlcCodeType.Error);
export const TLC_MODULE_COMPUTING_CARDINALITY = registerCode(2181, TlcCodeType.Error);
export const TLC_MODULE_EVALUATING = registerCode(2182, TlcCodeType.Error);
/** The %1% argument of %2% must be in the domain of its first argument:<br>%3%<br>, but instead it is<br>%4% */
export const TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN = registerCode(2183, TlcCodeType.Error);
export const TLC_MODULE_APPLY_EMPTY_SEQ = registerCode(2184, TlcCodeType.Error);

export const TLC_SYMMETRY_SET_TOO_SMALL = registerCode(2300, TlcCodeType.Warning);
export const TLC_SPECIFICATION_FEATURES_TEMPORAL_QUANTIFIER = registerCode(2301, TlcCodeType.Error);

export const TLC_STARTING = registerCode(2185, TlcCodeType.Info);
export const TLC_FINISHED = registerCode(2186, TlcCodeType.Info);

// distributed TLC

export const TLC_DISTRIBUTED_SERVER_RUNNING = registerCode(7000, TlcCodeType.Info);
export const TLC_DISTRIBUTED_WORKER_REGISTERED = registerCode(TLC_DISTRIBUTED_SERVER_RUNNING.num + 1, TlcCodeType.Info);
export const TLC_DISTRIBUTED_WORKER_DEREGISTERED
    = registerCode(TLC_DISTRIBUTED_WORKER_REGISTERED.num + 1, TlcCodeType.Info);
export const TLC_DISTRIBUTED_WORKER_STATS = registerCode(TLC_DISTRIBUTED_WORKER_DEREGISTERED.num + 1, TlcCodeType.Info);
export const TLC_DISTRIBUTED_SERVER_NOT_RUNNING = registerCode(TLC_DISTRIBUTED_WORKER_STATS.num + 1, TlcCodeType.Info);
export const TLC_DISTRIBUTED_VM_VERSION = registerCode(TLC_DISTRIBUTED_SERVER_NOT_RUNNING.num + 1, TlcCodeType.Ignore);
export const TLC_DISTRIBUTED_WORKER_LOST = registerCode(TLC_DISTRIBUTED_VM_VERSION.num + 1, TlcCodeType.Error);
export const TLC_DISTRIBUTED_EXCEED_BLOCKSIZE = registerCode(TLC_DISTRIBUTED_WORKER_LOST.num + 1, TlcCodeType.Error);
export const TLC_DISTRIBUTED_SERVER_FPSET_WAITING
    = registerCode(TLC_DISTRIBUTED_EXCEED_BLOCKSIZE.num + 1, TlcCodeType.Ignore);
export const TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED
    = registerCode(TLC_DISTRIBUTED_SERVER_FPSET_WAITING.num + 1, TlcCodeType.Ignore);
export const TLC_DISTRIBUTED_SERVER_FINISHED
    = registerCode(TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED.num + 1, TlcCodeType.Ignore);

// errors during parsing of the model configuration

export const CFG_ERROR_READING_FILE = registerCode(5001, TlcCodeType.Error);
export const CFG_GENERAL = registerCode(5002, TlcCodeType.Error);
export const CFG_MISSING_ID = registerCode(5003, TlcCodeType.Error);
export const CFG_TWICE_KEYWORD = registerCode(5004, TlcCodeType.Error);
export const CFG_EXPECT_ID = registerCode(5005, TlcCodeType.Error);
export const CFG_EXPECTED_SYMBOL = registerCode(5006, TlcCodeType.Error);
export const TLC_MODE_MC = registerCode(2187, TlcCodeType.Info);
export const TLC_MODE_MC_DFS = registerCode(2271, TlcCodeType.Ignore);
export const TLC_MODE_SIMU = registerCode(2188, TlcCodeType.Ignore);
export const TLC_COMPUTING_INIT = registerCode(2189, TlcCodeType.Info);
export const TLC_COMPUTING_INIT_PROGRESS = registerCode(2269, TlcCodeType.Info);
export const TLC_INIT_GENERATED1 = registerCode(2190, TlcCodeType.Info);
export const TLC_INIT_GENERATED2 = registerCode(2191, TlcCodeType.Info);
export const TLC_INIT_GENERATED3 = registerCode(2207, TlcCodeType.Info);
export const TLC_INIT_GENERATED4 = registerCode(2208, TlcCodeType.Info);
export const TLC_CHECKING_TEMPORAL_PROPS = registerCode(2192, TlcCodeType.Info);
export const TLC_CHECKING_TEMPORAL_PROPS_END = registerCode(2267, TlcCodeType.Ignore);
export const TLC_SUCCESS = registerCode(2193, TlcCodeType.Info);
export const TLC_SEARCH_DEPTH = registerCode(2194, TlcCodeType.Ignore);
export const TLC_STATE_GRAPH_OUTDEGREE = registerCode(2268, TlcCodeType.Ignore);
export const TLC_CHECKPOINT_START = registerCode(2195, TlcCodeType.Info);
export const TLC_CHECKPOINT_END = registerCode(2196, TlcCodeType.Ignore);
export const TLC_CHECKPOINT_RECOVER_START = registerCode(2197, TlcCodeType.Ignore);
export const TLC_CHECKPOINT_RECOVER_END = registerCode(2198, TlcCodeType.Ignore);
export const TLC_STATS = registerCode(2199, TlcCodeType.Ignore);
export const TLC_STATS_DFID = registerCode(2204, TlcCodeType.Ignore);
export const TLC_STATS_SIMU = registerCode(2210, TlcCodeType.Ignore);
export const TLC_PROGRESS_STATS = registerCode(2200, TlcCodeType.Info);
export const TLC_COVERAGE_START = registerCode(2201, TlcCodeType.Ignore);
export const TLC_COVERAGE_END = registerCode(2202, TlcCodeType.Ignore);
export const TLC_CHECKPOINT_RECOVER_END_DFID = registerCode(2203, TlcCodeType.Ignore);
export const TLC_PROGRESS_START_STATS_DFID = registerCode(2205, TlcCodeType.Ignore);
export const TLC_PROGRESS_STATS_DFID = registerCode(2206, TlcCodeType.Ignore);
export const TLC_PROGRESS_SIMU = registerCode(2209, TlcCodeType.Ignore);
export const TLC_FP_COMPLETED = registerCode(2211, TlcCodeType.Ignore);

export const TLC_LIVE_IMPLIED = registerCode(2212, TlcCodeType.Ignore);
export const TLC_LIVE_CANNOT_HANDLE_FORMULA = registerCode(2213, TlcCodeType.Error);
export const TLC_LIVE_WRONG_FORMULA_FORMAT = registerCode(2214, TlcCodeType.Error);
export const TLC_LIVE_ENCOUNTERED_ACTIONS = registerCode(2249, TlcCodeType.Error);
export const TLC_LIVE_STATE_PREDICATE_NON_BOOL = registerCode(2250, TlcCodeType.Error);
export const TLC_LIVE_CANNOT_EVAL_FORMULA = registerCode(2251, TlcCodeType.Error);
export const TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE = registerCode(2252, TlcCodeType.Error);
export const TLC_LIVE_FORMULA_TAUTOLOGY = registerCode(2253, TlcCodeType.Error);

export const TLC_EXPECTED_VALUE = registerCode(2215, TlcCodeType.Error);
export const TLC_EXPECTED_EXPRESSION = registerCode(2246, TlcCodeType.Error);
export const TLC_EXPECTED_EXPRESSION_IN_COMPUTING = registerCode(2247, TlcCodeType.Error);
export const TLC_EXPECTED_EXPRESSION_IN_COMPUTING2 = registerCode(2248, TlcCodeType.Error);

// state printing
export const TLC_STATE_PRINT1 = registerCode(2216, TlcCodeType.Info);
export const TLC_STATE_PRINT2 = registerCode(2217, TlcCodeType.Info);
export const TLC_STATE_PRINT3 = registerCode(2218, TlcCodeType.Info);
export const TLC_SANY_END = registerCode(2219, TlcCodeType.Info);
export const TLC_SANY_START = registerCode(2220, TlcCodeType.Info);
export const TLC_COVERAGE_MISMATCH = registerCode(2776, TlcCodeType.Ignore);
export const TLC_COVERAGE_VALUE = registerCode(2221, TlcCodeType.Ignore);
export const TLC_COVERAGE_VALUE_COST = registerCode(2775, TlcCodeType.Ignore);
export const TLC_COVERAGE_NEXT = registerCode(2772, TlcCodeType.Info);
export const TLC_COVERAGE_INIT = registerCode(2773, TlcCodeType.Info);
export const TLC_COVERAGE_PROPERTY = registerCode(2774, TlcCodeType.Ignore);
export const TLC_COVERAGE_END_OVERHEAD = registerCode(2777, TlcCodeType.Ignore);

// config file errors
export const TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM = registerCode(2222, TlcCodeType.Error);
export const TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID = registerCode(2223, TlcCodeType.Error);
export const TLC_CONFIG_WRONG_SUBSTITUTION = registerCode(2224, TlcCodeType.Error);
export const TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS = registerCode(2225, TlcCodeType.Error);
export const TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR = registerCode(2280, TlcCodeType.Error);
export const TLC_CONFIG_SUBSTITUTION_NON_CONSTANT = registerCode(2281, TlcCodeType.Error);
export const TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC = registerCode(2226, TlcCodeType.Error);
export const TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT = registerCode(2227, TlcCodeType.Error);
export const TLC_CONFIG_ID_REQUIRES_NO_ARG = registerCode(2228, TlcCodeType.Error);
export const TLC_CONFIG_SPECIFIED_NOT_DEFINED = registerCode(2229, TlcCodeType.Error);
export const TLC_CONFIG_ID_HAS_VALUE = registerCode(2230, TlcCodeType.Error);
export const TLC_CONFIG_MISSING_INIT = registerCode(2231, TlcCodeType.Error);
export const TLC_CONFIG_MISSING_NEXT = registerCode(2232, TlcCodeType.Error);
export const TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT = registerCode(2233, TlcCodeType.Error);
export const TLC_CONFIG_OP_NO_ARGS = registerCode(2234, TlcCodeType.Error);
export const TLC_CONFIG_OP_NOT_IN_SPEC = registerCode(2235, TlcCodeType.Error);
export const TLC_CONFIG_OP_IS_EQUAL = registerCode(2236, TlcCodeType.Error);
export const TLC_CONFIG_SPEC_IS_TRIVIAL = registerCode(2237, TlcCodeType.Error);
export const TLC_CANT_HANDLE_SUBSCRIPT = registerCode(2238, TlcCodeType.Error);
export const TLC_CANT_HANDLE_CONJUNCT = registerCode(2239, TlcCodeType.Error);
export const TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS = registerCode(2240, TlcCodeType.Error);
export const TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED = registerCode(2241, TlcCodeType.Error);
export const TLC_CONFIG_OP_ARITY_INCONSISTENT = registerCode(2242, TlcCodeType.Error);
export const TLC_CONFIG_NO_STATE_TYPE = registerCode(2243, TlcCodeType.Error);
export const TLC_CANT_HANDLE_REAL_NUMBERS = registerCode(2244, TlcCodeType.Error);
export const TLC_NO_MODULES = registerCode(2245, TlcCodeType.Error);

export const TLC_ENABLED_WRONG_FORMULA = registerCode(2260, TlcCodeType.Error);
export const TLC_ENCOUNTERED_FORMULA_IN_PREDICATE = registerCode(2261, TlcCodeType.Error);
export const TLC_VERSION = registerCode(2262, TlcCodeType.Ignore);
export const TLC_USAGE = registerCode(2263, TlcCodeType.Ignore);
export const TLC_COUNTER_EXAMPLE = registerCode(2264, TlcCodeType.Ignore);  // It will be shown in error trace

export const TLC_INTEGER_TOO_BIG = registerCode(2265, TlcCodeType.Error);
export const TLC_TRACE_TOO_LONG = registerCode(2282, TlcCodeType.Error);

export const TLC_ENVIRONMENT_JVM_GC = registerCode(2401, TlcCodeType.Warning);

function registerCode(num: number, type: TlcCodeType): TlcCode {
    const tlcCode = new TlcCode(num, type);
    TLC_CODES.set(num, tlcCode);
    return tlcCode;
}
