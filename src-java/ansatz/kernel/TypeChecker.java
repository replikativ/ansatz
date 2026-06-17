// Ansatz kernel — Type inference and definitional equality.

package ansatz.kernel;

import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Type checker implementing bidirectional type inference and definitional equality.
 * Port of tc.clj with Lean 4's lazy delta reduction algorithm.
 *
 * <p>Key improvement over the Clojure implementation: lazy delta reduction
 * unfolds ONE side at a time based on reducibility hints, often avoiding
 * unnecessary unfolding entirely.
 */
public final class TypeChecker {
    static final byte DEFN_SAFE = 0;
    static final byte DEFN_UNSAFE = 1;
    static final byte DEFN_PARTIAL = 2;

    private final Env env;
    private final Reducer reducer;
    private final EquivManager eqvManager;
    private final IdentityHashMap<Expr, Expr> inferIdentityCache;      // exact object fast path
    private final HashMap<LeanExprKey, Expr> inferStructuralCache;     // Lean expr_map equality, identity fast path above
    private final IdentityHashMap<Expr, Expr> inferOnlyIdentityCache;  // exact object fast path
    private final HashMap<LeanExprKey, Expr> inferOnlyStructuralCache; // Lean expr_map equality, identity fast path above
    private final IdentityHashMap<Expr, IdentityHashMap<Expr, Boolean>> failureIdentityCache;
    private final HashMap<LeanExprKey, HashMap<LeanExprKey, Boolean>> failureStructuralCache;
    private long nextId;
    private int isDefEqDepth;
    private final byte definitionSafety;
    private final HashSet<Object> allowedLevelParams;
    public boolean tracing;

    // isDefEq diagnostic counters
    long isDefEqCalls;
    long isDefEqQuickHits;    // pointer equality or hash mismatch
    long isDefEqEquivHits;    // EquivManager hits
    long isDefEqProofIrrelHits;
    long[] isDefEqDepthHist = new long[500]; // histogram: calls at each depth
    // Per-step resolution counters for depth >= STEP_DIAG_DEPTH
    static final int STEP_DIAG_DEPTH = 45;
    long stepDiagTotal;      // total calls at depth >= STEP_DIAG_DEPTH
    long stepDiagQuick;      // resolved by quick (pointer eq or equiv manager)
    long stepDiagProofIrrel; // resolved by proof irrelevance
    long stepDiagLazyDelta;  // resolved by lazy delta
    long stepDiagWhnfCore2;  // resolved by second whnfCore pass
    long stepDiagApp;        // resolved by app congruence
    long stepDiagBinding;    // resolved by binding
    long stepDiagEta;        // resolved by eta
    long stepDiagUnit;       // resolved by unit-like
    long stepDiagFail;       // returned false
    // Diagnostic: capture expression shape at depth DIAG_CAPTURE_MIN_DEPTH
    public java.util.ArrayList<String[]> diagCaptures = new java.util.ArrayList<>();
    private static final int DIAG_CAPTURE_LIMIT = 30;
    private static final int DIAG_CAPTURE_MIN_DEPTH = 50;
    private int traceCount;
    public int traceLimit = 200;
    public int traceMinDepth = 0;  // only trace at this depth or higher

    // Local context: fvar id -> [tag, name, type, value?]
    private HashMap<Long, Object[]> lctx;

    // Eager reduce mode: set when argument is eagerReduce _ _ (Lean 4 type_checker.cpp:168-170)
    private boolean eagerReduce;

    // Structured NDJSON trace output — write one JSON line per isDefEq call
    private Writer traceWriter;
    private long traceSeq;
    private boolean phaseTracing;

    private static final boolean TRACE_FULL =
        Boolean.getBoolean("ansatz.kernel.trace.full");
    private static final boolean TRACE_DELTA =
        Boolean.getBoolean("ansatz.kernel.trace.delta");
    private static final String TRACE_DELTA_FILTER =
        System.getProperty("ansatz.kernel.trace.delta.filter", "");
    private static final String TRACE_EQV_FILTER =
        System.getProperty("ansatz.kernel.trace.equiv.filter", "");
    private static final boolean TRACE_BINDING =
        Boolean.getBoolean("ansatz.kernel.trace.binding");
    private final Expr[] traceLhsStack = new Expr[1024];
    private final Expr[] traceRhsStack = new Expr[1024];

    private static final long DEFAULT_FUEL = 5_000_000L;
    private static final int MAX_ISDEFEQ_DEPTH = 50000;

    /** Enable tracing with limit and optional min depth filter. */
    public void setTracing(boolean on, int limit, int minDepth) {
        this.tracing = on;
        this.traceLimit = limit;
        this.traceMinDepth = minDepth;
        this.traceCount = 0;
    }
    public void setTracing(boolean on, int limit) { setTracing(on, limit, 0); }

    /** Enable structured NDJSON tracing to a Writer (e.g. FileWriter).
     *  Each isDefEq call emits one JSON line:
     *  {"s":seq,"d":depth,"l":"lhs_fp","r":"rhs_fp","res":bool,"by":"step"}
     *  Call with null to disable. */
    public void setTraceWriter(Writer w) {
        this.traceWriter = w;
        this.traceSeq = 0;
    }

    public void setPhaseTracing(boolean on) {
        this.phaseTracing = on;
    }

    private void emitPhase(String phase) {
        if (!phaseTracing || traceWriter == null) return;
        try {
            traceWriter.write("{\"phase\":\"" + jsonEsc(phase) + "\"}\n");
        } catch (IOException e) {
            // ignore trace write failures
        }
    }

    private void emitPhaseTypes(String phase, Expr a, Expr b) {
        if (!phaseTracing || traceWriter == null) return;
        try {
            traceWriter.write("{\"phase\":\"" + jsonEsc(phase) +
                "\",\"a\":\"" + jsonEsc(exprFingerprint(a, 6)) +
                "\",\"b\":\"" + jsonEsc(exprFingerprint(b, 6)) + "\"}\n");
        } catch (IOException e) {
            // ignore trace write failures
        }
    }

    private void emitPhasePairStats(String phase, Expr a, Expr b) {
        if (!phaseTracing || traceWriter == null) return;
        try {
            Object[] aFA = Reducer.getAppFnArgs(a);
            Object[] bFA = Reducer.getAppFnArgs(b);
            Expr aHead = (Expr) aFA[0];
            Expr bHead = (Expr) bFA[0];
            Expr[] aArgs = (Expr[]) aFA[1];
            Expr[] bArgs = (Expr[]) bFA[1];
            traceWriter.write("{\"phase\":\"" + jsonEsc(phase) +
                "\",\"eqp\":" + (a.isEqp(b) ? "true" : "false") +
                ",\"deepEq\":" + (exprDeepEquals(a, b) ? "true" : "false") +
                ",\"aHash\":" + a.structuralHash() +
                ",\"bHash\":" + b.structuralHash() +
                ",\"aStore\":" + a.storeId +
                ",\"bStore\":" + b.storeId +
                ",\"aHead\":\"" + jsonEsc(exprFingerprint(aHead, 4)) +
                "\",\"bHead\":\"" + jsonEsc(exprFingerprint(bHead, 4)) +
                "\",\"headEqp\":" + (aHead.isEqp(bHead) ? "true" : "false") +
                ",\"headDeepEq\":" + (exprDeepEquals(aHead, bHead) ? "true" : "false") +
                ",\"aArgs\":" + aArgs.length +
                ",\"bArgs\":" + bArgs.length +
                "}\n");
        } catch (IOException e) {
            // ignore trace write failures
        }
    }

    /** Emit a structured trace event. */
    private void emitTrace(String lhs, String rhs, boolean result, String resolvedBy) {
        if (traceWriter == null) return;
        try {
            StringBuilder sb = new StringBuilder(256);
            sb.append("{\"s\":").append(traceSeq++);
            sb.append(",\"d\":").append(isDefEqDepth);
            sb.append(",\"l\":\"").append(jsonEsc(lhs));
            sb.append("\",\"r\":\"").append(jsonEsc(rhs));
            sb.append("\",\"res\":").append(result);
            sb.append(",\"by\":\"").append(resolvedBy).append("\"");
            if (TRACE_FULL && isDefEqDepth >= 0 && isDefEqDepth < traceLhsStack.length) {
                Expr curL = traceLhsStack[isDefEqDepth];
                Expr curR = traceRhsStack[isDefEqDepth];
                if (curL != null && curR != null) {
                    sb.append(",\"lFull\":\"").append(jsonEscLimit(exprFingerprint(curL, 8), 4000)).append("\"");
                    sb.append(",\"rFull\":\"").append(jsonEscLimit(exprFingerprint(curR, 8), 4000)).append("\"");
                }
                int parentDepth = isDefEqDepth - 1;
                if (parentDepth >= 0) {
                    Expr parentL = traceLhsStack[parentDepth];
                    Expr parentR = traceRhsStack[parentDepth];
                    if (parentL != null && parentR != null) {
                        sb.append(",\"parentL\":\"").append(jsonEscLimit(exprFingerprint(parentL, 8), 4000)).append("\"");
                        sb.append(",\"parentR\":\"").append(jsonEscLimit(exprFingerprint(parentR, 8), 4000)).append("\"");
                    }
                }
            }
            sb.append("}\n");
            traceWriter.write(sb.toString());
        } catch (IOException e) {
            // silently ignore write failures
        }
    }

    private void emitDeltaTrace(String stage, Expr lhs, Expr rhs) {
        if (!TRACE_DELTA || traceWriter == null) return;
        String l = exprFingerprint(lhs, 6);
        String r = exprFingerprint(rhs, 6);
        if (!TRACE_DELTA_FILTER.isEmpty()
            && !l.contains(TRACE_DELTA_FILTER)
            && !r.contains(TRACE_DELTA_FILTER)) {
            return;
        }
        try {
            traceWriter.write("{\"delta\":\"" + jsonEsc(stage) +
                "\",\"d\":" + isDefEqDepth +
                ",\"l\":\"" + jsonEscLimit(l, 4000) +
                "\",\"r\":\"" + jsonEscLimit(r, 4000) + "\"}\n");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void emitEquivTrace(String phase, Expr lhs, Expr rhs) {
        if (traceWriter == null || TRACE_EQV_FILTER.isEmpty()) return;
        String l = exprFingerprint(lhs, 12);
        String r = exprFingerprint(rhs, 12);
        if (!l.contains(TRACE_EQV_FILTER) && !r.contains(TRACE_EQV_FILTER)) return;
        try {
            traceWriter.write("{\"phase\":\"" + jsonEsc(phase) +
                "\",\"d\":" + isDefEqDepth +
                ",\"l\":\"" + jsonEscLimit(l, 4000) +
                "\",\"r\":\"" + jsonEscLimit(r, 4000) +
                "\"," + eqvManager.debugStateJson(lhs, rhs) + "}\n");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void emitBindingDomainTrace(Expr t, Expr s, Expr domT, Expr domS) {
        if (!TRACE_BINDING || traceWriter == null) return;
        try {
            traceWriter.write("{\"binding_domain\":\"check\"" +
                ",\"ptr_eq\":" + domT.isEqp(domS) +
                ",\"object_eq\":" + (domT == domS) +
                ",\"same_store\":" + (domT.storeId >= 0 && domT.storeId == domS.storeId) +
                ",\"deepEq\":" + exprDeepEquals(domT, domS) +
                ",\"depth\":" + isDefEqDepth +
                ",\"t\":\"" + jsonEscLimit(exprFingerprint(t, 6), 4000) +
                "\",\"s\":\"" + jsonEscLimit(exprFingerprint(s, 6), 4000) +
                "\",\"domT\":\"" + jsonEscLimit(exprFingerprint(domT, 6), 4000) +
                "\",\"domS\":\"" + jsonEscLimit(exprFingerprint(domS, 6), 4000) +
                "\",\"domTStore\":" + domT.storeId +
                ",\"domSStore\":" + domS.storeId +
                "}\n");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /** Minimal JSON string escaping. */
    private static String jsonEsc(String s) {
        return jsonEscLimit(s, 200);
    }

    private static String jsonEscLimit(String s, int maxLen) {
        if (s.length() > maxLen) s = s.substring(0, maxLen) + "...";
        return s.replace("\\", "\\\\").replace("\"", "\\\"")
                .replace("\n", "\\n").replace("\r", "\\r");
    }

    /** Canonical expression fingerprint for trace comparison.
     *  Produces the same string from both kernels for the same expression.
     *  Uses: kind + name (for const), index (for bvar/proj), depth-limited structure. */
    /** Level fingerprint matching Lean's pp format:
     *  zero→0, succ(zero)→1, succ(u)→succ u, max(a,b)→max a b, imax(a,b)→imax a b
     *  Compound levels (max/imax) are parenthesized when used as arguments. */
    public static String levelFingerprint(Level l) { return levelPrint(l); }

    /** Match Lean's level pretty printer: print_child adds parens for non-atomic levels. */
    private static String levelPrintChild(Level l) {
        if (Level.toNat(l) >= 0 || l.tag == Level.PARAM) {
            return levelPrint(l);
        }
        return "(" + levelPrint(l) + ")";
    }

    /** Match Lean's level pretty printer exactly (level.cpp:339-369). */
    private static String levelPrint(Level l) {
        if (l == null) return "?";
        // is_explicit: pure number with no params
        long n = Level.toNat(l);
        if (n >= 0) return Long.toString(n);
        switch (l.tag) {
            case Level.PARAM: return l.o0.toString();
            case Level.SUCC: {
                return "succ " + levelPrintChild(l.succPred());
            }
            case Level.MAX: case Level.IMAX: {
                StringBuilder sb = new StringBuilder();
                sb.append(l.tag == Level.MAX ? "max " : "imax ");
                sb.append(levelPrintChild((Level) l.o0));
                // Flatten right-associative same-kind nodes
                Level rhs = (Level) l.o1;
                while (rhs.tag == l.tag) {
                    sb.append(" ");
                    sb.append(levelPrintChild((Level) rhs.o0));
                    rhs = (Level) rhs.o1;
                }
                sb.append(" ");
                sb.append(levelPrintChild(rhs));
                return sb.toString();
            }
            default: return "?level";
        }
    }

    public static String exprFingerprint(Expr e) { return exprFingerprint(e, 3); }
    public static String exprFingerprint(Expr e, int maxDepth) {
        if (e == null) return "null";
        if (maxDepth <= 0) return "_";
        switch (e.tag) {
            case Expr.BVAR: return "#" + e.longVal;
            case Expr.SORT: return "Sort(" + levelFingerprint((Level) e.o0) + ")";
            case Expr.CONST: {
                String name = e.o0.toString();
                Object[] lvls = Reducer.constLevels(e);
                if (lvls.length == 0) return name;
                StringBuilder sb = new StringBuilder(name).append(".{");
                for (int i = 0; i < lvls.length; i++) {
                    if (i > 0) sb.append(",");
                    sb.append(levelFingerprint((Level) lvls[i]));
                }
                return sb.append("}").toString();
            }
            case Expr.FVAR: return "fvar(_kernel_fresh." + e.longVal + ")";
            case Expr.LIT_NAT: return "nat(" + e.o0 + ")";
            case Expr.LIT_STR: return "str";
            case Expr.APP: {
                // Flatten app spine
                Object[] fa = Reducer.getAppFnArgs(e);
                Expr fn = (Expr) fa[0];
                Expr[] args = (Expr[]) fa[1];
                StringBuilder sb = new StringBuilder();
                sb.append("@(").append(exprFingerprint(fn, maxDepth - 1));
                for (Expr arg : args) {
                    sb.append(" ").append(exprFingerprint(arg, maxDepth - 1));
                }
                return sb.append(")").toString();
            }
            case Expr.LAM:
                return "fun(" + exprFingerprint((Expr) e.o1, maxDepth - 1) + "," +
                       exprFingerprint((Expr) e.o2, maxDepth - 1) + ")";
            case Expr.FORALL:
                return "Pi(" + exprFingerprint((Expr) e.o1, maxDepth - 1) + "," +
                       exprFingerprint((Expr) e.o2, maxDepth - 1) + ")";
            case Expr.LET:
                return "let(" + exprFingerprint((Expr) e.o1, maxDepth - 1) + "," +
                       exprFingerprint((Expr) e.o2, maxDepth - 1) + "," +
                       exprFingerprint((Expr) e.o3, maxDepth - 1) + ")";
            case Expr.PROJ:
                return e.o0 + "." + e.longVal + "(" +
                       exprFingerprint((Expr) e.o1, maxDepth - 1) + ")";
            case Expr.MDATA:
                return "mdata(" + exprFingerprint((Expr) e.o1, maxDepth - 1) + ")";
            default: return "?tag" + e.tag;
        }
    }

    private void trace(String msg) {
        if (tracing && traceCount < traceLimit && isDefEqDepth >= traceMinDepth) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < Math.min(isDefEqDepth, 40); i++) sb.append(' ');
            sb.append(msg);
            System.out.println(sb.toString());
            System.out.flush();
            traceCount++;
        }
    }

    /** Summarize expression for tracing. Shows structure up to configurable depth. */
    public static String exprSummary(Expr e) { return exprSummary(e, 2); }
    public static String exprSummary(Expr e, int maxDepth) {
        if (e == null) return "null";
        if (maxDepth <= 0) return "...";
        switch (e.tag) {
            case Expr.BVAR: return "bvar(" + e.longVal + ")";
            case Expr.SORT: return "sort(" + e.o0 + ")";
            case Expr.CONST: return "const(" + e.o0 + ")";
            case Expr.FVAR: return "fvar(" + e.longVal + ")";
            case Expr.LIT_NAT: return "nat(" + e.o0 + ")";
            case Expr.LIT_STR: return "str(\"" + e.o0 + "\")";
            case Expr.LAM: return "lam(" + exprSummary((Expr) e.o2, maxDepth - 1) + ")";
            case Expr.FORALL: return "forall(" + exprSummary((Expr) e.o2, maxDepth - 1) + ")";
            case Expr.APP: {
                Object[] fa = Reducer.getAppFnArgs(e);
                Expr fn = (Expr) fa[0];
                Expr[] args = (Expr[]) fa[1];
                StringBuilder sb = new StringBuilder();
                sb.append("@(").append(exprSummary(fn, maxDepth - 1));
                for (int i = 0; i < args.length && i < 3; i++) {
                    sb.append(" ").append(exprSummary(args[i], maxDepth - 1));
                }
                if (args.length > 3) sb.append(" ..+" + (args.length - 3));
                sb.append(")");
                return sb.toString();
            }
            case Expr.LET: return "let(" + exprSummary((Expr) e.o2, maxDepth - 1) + ")";
            case Expr.PROJ: return "proj(" + e.o0 + "," + e.longVal + "," +
                                    exprSummary((Expr) e.o1, maxDepth - 1) + ")";
            case Expr.MDATA: return "mdata(" + exprSummary((Expr) e.o1, maxDepth - 1) + ")";
            default: return "tag" + e.tag;
        }
    }

    /** Check if expression is of the form eagerReduce _ _ (Lean 4 type_checker.cpp:159-160) */
    private static boolean isEagerReduce(Expr e) {
        // eagerReduce applied to 2 args
        if (e.tag != Expr.APP) return false;
        Expr fn = e;
        int nargs = 0;
        while (fn.tag == Expr.APP) { fn = (Expr) fn.o0; nargs++; }
        return nargs == 2 && fn.tag == Expr.CONST && fn.o0 == Name.EAGER_REDUCE;
    }

    /** Look up fvar in local context. Returns [tag, name, type, value?] or null. */
    public Object[] lookupFvar(long id) { return lctx.get(id); }

    /** Get the reducer for REPL debugging. */
    public Reducer getReducer() { return reducer; }

    /** Set transparency mode on the reducer.
     *  0 = reducible (most restrictive), 1 = default, 2 = all. */
    public void setTransparency(int mode) { reducer.setTransparency(mode); }

    /** Set the delta-reduction allow list for reducible mode (transparency=0).
     *  Only names in this set will be unfolded. */
    public void setDeltaAllowSet(java.util.HashSet<Name> names) { reducer.setDeltaAllowSet(names); }

    /** Get isDefEq depth for debugging. */
    public int getIsDefEqDepth() { return isDefEqDepth; }

    public TypeChecker(Env env) {
        this(env, DEFN_SAFE, null);
    }

    public TypeChecker(Env env, byte definitionSafety) {
        this(env, definitionSafety, null);
    }

    public TypeChecker(Env env, byte definitionSafety, Object[] allowedLevelParams) {
        this.env = env;
        this.definitionSafety = definitionSafety;
        this.allowedLevelParams = mkAllowedLevelParamSet(allowedLevelParams);
        this.reducer = new Reducer(env);
        this.eqvManager = new EquivManager();
        this.inferIdentityCache = new IdentityHashMap<>(1024);
        this.inferStructuralCache = new HashMap<>(1024);
        this.inferOnlyIdentityCache = new IdentityHashMap<>(1024);
        this.inferOnlyStructuralCache = new HashMap<>(1024);
        this.failureIdentityCache = new IdentityHashMap<>(256);
        this.failureStructuralCache = new HashMap<>(256);
        this.nextId = 0;
        this.lctx = new HashMap<>();
        this.reducer.setLctx(this.lctx);
        this.reducer.setCallbacks(this::inferTypeOnly, this::isDefEq);
    }

    private static HashSet<Object> mkAllowedLevelParamSet(Object[] levelParams) {
        if (levelParams == null) return null;
        HashSet<Object> allowed = new HashSet<>(levelParams.length * 2 + 1);
        for (Object lp : levelParams) {
            allowed.add(lp);
        }
        return allowed;
    }

    private void checkLevel(Level l) {
        if (allowedLevelParams == null) return;
        Object undef = getUndefinedLevelParam(l);
        if (undef != null) {
            throw new RuntimeException("Type error: invalid reference to undefined universe level parameter '" + undef + "'");
        }
    }

    private Object getUndefinedLevelParam(Level l) {
        switch (l.tag) {
            case Level.ZERO:
                return null;
            case Level.SUCC:
                return getUndefinedLevelParam(l.succPred());
            case Level.MAX: {
                Object lhs = getUndefinedLevelParam(l.maxLhs());
                return lhs != null ? lhs : getUndefinedLevelParam(l.maxRhs());
            }
            case Level.IMAX: {
                Object lhs = getUndefinedLevelParam(l.imaxLhs());
                return lhs != null ? lhs : getUndefinedLevelParam(l.imaxRhs());
            }
            case Level.PARAM:
                return allowedLevelParams.contains(l.paramName()) ? null : l.paramName();
            default:
                return null;
        }
    }

    public void setFuel(long fuel) {
        this.reducer.setFuel(fuel);
    }

    public long getFuelUsed() {
        return this.reducer.getFuelUsed();
    }

    /** Get instrumentation counters from the Reducer. */
    public HashMap<String, Long> getReducerStats() {
        HashMap<String, Long> stats = this.reducer.getStats();
        stats.put("isDefEq-calls", isDefEqCalls);
        stats.put("isDefEq-quick-hits", isDefEqQuickHits);
        // Per-step resolution counters at depth >= STEP_DIAG_DEPTH
        if (stepDiagTotal > 0) {
            stats.put("step-diag-total", stepDiagTotal);
            stats.put("step-diag-quick", stepDiagQuick);
            stats.put("step-diag-proof-irrel", stepDiagProofIrrel);
            stats.put("step-diag-lazy-delta", stepDiagLazyDelta);
            stats.put("step-diag-whnfcore2", stepDiagWhnfCore2);
            stats.put("step-diag-app", stepDiagApp);
            stats.put("step-diag-binding", stepDiagBinding);
            stats.put("step-diag-eta", stepDiagEta);
            stats.put("step-diag-unit", stepDiagUnit);
            stats.put("step-diag-fail", stepDiagFail);
        }
        // Depth histogram: emit depth buckets with non-zero counts
        for (int d = 0; d < isDefEqDepthHist.length; d++) {
            if (isDefEqDepthHist[d] > 0)
                stats.put("depth-" + d, isDefEqDepthHist[d]);
        }
        return stats;
    }

    /** Get the max whnf recursion depth. */
    public int getReducerMaxDepth() {
        return this.reducer.whnfMaxDepth;
    }

    /** Get the expression that triggered the maximum whnf depth. */
    public Expr getReducerMaxDepthExpr() {
        return this.reducer.getMaxDepthExpr();
    }

    private long freshId() { return nextId++; }

    private void reserveLocalId(long id) {
        if (id >= nextId) nextId = id + 1;
    }

    /**
     * Return true iff e is a proposition (its type is Prop).
     * Matches Lean 4's type_checker::is_prop.
     */
    private boolean isProp(Expr e) {
        Expr t = whnf(inferTypeOnly(e));
        return t.tag == Expr.SORT && ((Level) t.o0).tag == Level.ZERO;
    }

    // ============================================================
    // WHNF delegation
    // ============================================================

    private Expr whnf(Expr e) {
        return reducer.whnf(e);
    }

    private Expr whnfCore(Expr e) {
        return reducer.whnfCore(e);
    }

    // ============================================================
    // Local context management
    // ============================================================

    private void lctxAddLocal(long id, Object name, Expr type) {
        reserveLocalId(id);
        lctx.put(id, new Object[]{0, name, type});
    }

    /** Public API: register a local declaration in the type checker's local context. */
    public void addLocal(long id, String name, Expr type) {
        lctxAddLocal(id, name, type);
        reducer.setLctx(lctx);
    }

    /** Generate a fresh fvar id. */
    public long nextFvarId() { return freshId(); }

    /** Get the environment. */
    public Env getEnv() { return env; }

    /** Add a local declaration (convenience for validation code). */
    public void addLocalDecl(long id, Object name, Expr type) {
        lctxAddLocal(id, name, type);
        reducer.setLctx(lctx);
    }

    private void lctxAddLet(long id, Object name, Expr type, Expr value) {
        reserveLocalId(id);
        lctx.put(id, new Object[]{1, name, type, value});
    }

    private void lctxRemove(long id) {
        lctx.remove(id);
    }

    // ============================================================
    // mk_binding: reconstruct Pi/Let around body after abstracting fvars
    // Matches Lean 4's local_ctx::mk_binding (local_ctx.cpp:94-117)
    // ============================================================

    /**
     * Reconstruct Pi binders (or Let binders for let-decls) around body,
     * abstracting fvarIds. When removeDeadLet=true, let bindings that
     * aren't referenced in the body are dropped.
     */
    private Expr mkPi(long[] fvarIds, int n, Expr body, boolean removeDeadLet) {
        // Step 1: abstract all fvars in the body
        Expr r = Reducer.abstractFvars(body, n, fvarIds);
        // Step 2: wrap in binders from innermost to outermost
        int i = n;
        while (i > 0) {
            --i;
            Object[] decl = lctx.get(fvarIds[i]);
            int tag = (int) decl[0]; // 0=local, 1=let
            if (tag == 1) {
                // Let binding
                if (!removeDeadLet || r.bvarRange() > 0) {
                    Expr type = Reducer.abstractFvars((Expr) decl[2], i, fvarIds);
                    Expr value = Reducer.abstractFvars((Expr) decl[3], i, fvarIds);
                    r = Expr.mkLet(decl[1], type, value, r);
                } else {
                    r = Reducer.lowerLooseBVars(r, 1, 1);
                }
            } else {
                // Local binding — make a Pi
                Expr type = Reducer.abstractFvars((Expr) decl[2], i, fvarIds);
                // Need binder info — stored where? We use default for now.
                // For infer_lambda, the binder info comes from the original lambda.
                // We'll pass it via the decl array.
                Object binderInfo = decl.length > 3 ? decl[3] : null;
                r = Expr.forall(decl[1], type, r, binderInfo);
            }
        }
        return r;
    }

    /**
     * Add a local to lctx with binder info preserved (for mkPi reconstruction).
     */
    private void lctxAddLocalWithInfo(long id, Object name, Expr type, Object binderInfo) {
        reserveLocalId(id);
        lctx.put(id, new Object[]{0, name, type, binderInfo});
    }

    // ============================================================
    // Type inference
    // ============================================================

    /**
     * Infer type in infer-only mode (Lean's infer_type → infer_type_core(e, true)).
     * LENIENT BY DESIGN: assumes the input is well-formed and does NOT re-typecheck it — a fast
     * type COMPUTATION for elaboration/tactics, exactly like Lean's Meta.inferType. It is NOT a
     * verifier: it can return a type for an ill-typed term. NEVER gate validity / declaration
     * admission on this. The sole admission door is full checking — {@link #checkConstant}
     * (Clojure: env/check-constant, env/verifies?). Kept named inferType for fidelity to Lean.
     */
    public Expr inferType(Expr e) {
        return inferTypeCore(e, true);
    }

    /**
     * Fully check e and return its type (Lean's check → infer_type_core(e, false)).
     * Use this at declaration admission boundaries.
     */
    public Expr check(Expr e) {
        return inferTypeCore(e, false);
    }

    /**
     * Infer-only mode — used from isDefEq (Lean's infer_type()).
     * Matches Lean's infer_type_core(e, true).
     * Skips isDefEq checks in APP, sort checks in LAM, etc.
     */
    private Expr inferTypeOnly(Expr e) {
        return inferTypeCore(e, true);
    }

    private Expr inferTypeCore(Expr e, boolean inferOnly) {
        IdentityHashMap<Expr, Expr> identityCache = inferOnly ? inferOnlyIdentityCache : inferIdentityCache;
        HashMap<LeanExprKey, Expr> structuralCache = inferOnly ? inferOnlyStructuralCache : inferStructuralCache;
        Expr cached = identityCache.get(e);
        if (cached != null) return cached;
        cached = structuralCache.get(new LeanExprKey(e));
        if (cached != null) return cached;

        Expr result;
        switch (e.tag) {
            case Expr.BVAR:
                throw new RuntimeException("Type error: Loose bound variable in infer-type");

            case Expr.SORT:
                if (!inferOnly) {
                    checkLevel((Level) e.o0);
                }
                result = Expr.sort(Level.succ((Level) e.o0), Level.hasParam(Level.succ((Level) e.o0)));
                break;

            case Expr.CONST: {
                ConstantInfo ci = env.lookupOrThrow((Name) e.o0);
                Object[] levels = Reducer.constLevels(e);
                if (ci.levelParams.length != levels.length) {
                    throw new RuntimeException("Type error: Universe level mismatch for " + e.o0 +
                        " expected=" + ci.levelParams.length + " actual=" + levels.length +
                        " levels=" + java.util.Arrays.toString(levels));
                }
                if (!inferOnly) {
                    if (ci.isUnsafe && definitionSafety != DEFN_UNSAFE) {
                        throw new RuntimeException("Type error: invalid declaration, it uses unsafe declaration '" + e.o0 + "'");
                    }
                    if (ci.isDef() && ci.safety == DEFN_PARTIAL && definitionSafety == DEFN_SAFE) {
                        throw new RuntimeException("Type error: invalid declaration, safe declaration must not contain partial declaration '" + e.o0 + "'");
                    }
                    for (Object level : levels) {
                        checkLevel((Level) level);
                    }
                }
                if (ci.levelParams.length == 0) {
                    result = Expr.deepReIntern(ci.type);
                } else {
                    HashMap<Object, Level> subst = new HashMap<>(ci.levelParams.length * 2);
                    for (int i = 0; i < ci.levelParams.length; i++) {
                        subst.put(ci.levelParams[i], (Level) levels[i]);
                    }
                    result = Expr.deepReIntern(Reducer.instantiateLevelParams(ci.type, subst));
                }
                break;
            }

            case Expr.APP: {
                if (!inferOnly) {
                    // Full checking mode: check argument type matches domain
                    // Matching Lean's infer_app (type_checker.cpp:197-211)
                    Expr fType = ensurePiExpr(inferTypeCore((Expr) e.o0, false));
                    Expr argType = inferTypeCore((Expr) e.o1, false);
                    Expr dType = (Expr) fType.o1; // binding_domain
                    // Check if argument is eagerReduce _ _ (Lean 4 type_checker.cpp:168-174)
                    boolean prevEager = this.eagerReduce;
                    if (isEagerReduce((Expr) e.o1)) {
                        this.eagerReduce = true;
                    }
                    try {
                        emitPhase("inferApp.argDefEq");
                        emitPhaseTypes("inferApp.argDefEq.types", argType, dType);
                        if (!isDefEq(argType, dType)) {
                            Expr fn = e;
                            while (fn.tag == Expr.APP) fn = (Expr) fn.o0;
                            String fnStr = fn.tag == Expr.CONST ? fn.o0.toString() : ("tag=" + fn.tag);
                            Expr argW = whnf(argType);
                            Expr domW = whnf(dType);
                            String argTypeStr = argW.toString();
                            String domTypeStr = domW.toString();
                            if (argTypeStr.length() > 500) argTypeStr = argTypeStr.substring(0, 500) + "...";
                            if (domTypeStr.length() > 500) domTypeStr = domTypeStr.substring(0, 500) + "...";
                            throw new RuntimeException("Type error: Type mismatch in application of " + fnStr +
                                "\n  argType(whnf): " + argTypeStr + "\n  domType(whnf): " + domTypeStr);
                        }
                    } finally {
                        this.eagerReduce = prevEager;
                    }
                    result = Reducer.instantiate1((Expr) fType.o2, (Expr) e.o1); // binding_body
                } else {
                    // Infer-only mode: fast path (Lean type_checker.cpp:213-229)
                    // Skip through Pi binders without instantiating where possible.
                    Object[] fa = Reducer.getAppFnArgs(e);
                    Expr fn = (Expr) fa[0];
                    Expr[] args = (Expr[]) fa[1];
                    Expr fType = inferTypeCore(fn, true);
                    int j = 0;
                    int nargs = args.length;
                    for (int i = 0; i < nargs; i++) {
                        if (fType.tag == Expr.FORALL) {
                            fType = (Expr) fType.o2; // binding_body — skip without instantiating
                        } else {
                            // Need to instantiate accumulated args and whnf to get a Pi
                            fType = Reducer.instantiateRev(fType, i - j, args, j);
                            Expr piExpr = whnf(fType);
                            if (piExpr.tag != Expr.FORALL) {
                                throw new RuntimeException("Type error: Function expected in infer-only app");
                            }
                            fType = (Expr) piExpr.o2; // binding_body
                            j = i;
                        }
                    }
                    result = Reducer.instantiateRev(fType, nargs - j, args, j);
                }
                break;
            }

            case Expr.LAM: {
                // Matching Lean 4's infer_lambda (type_checker.cpp:150-166)
                java.util.ArrayList<Long> fvarIdList = new java.util.ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.LAM) {
                    Expr[] fvarArr = fvarIdList.isEmpty() ? new Expr[0] :
                        fvarIdList.stream().map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr d = Reducer.instantiateRev(
                        (Expr) cur.o1, fvarArr.length, fvarArr, 0);
                    long fvId = freshId();
                    Expr fv = Expr.fvar(fvId);
                    lctxAddLocalWithInfo(fvId, cur.o0, d, cur.o3);
                    fvarIdList.add(fvId);
                    if (!inferOnly) {
                        ensureSort(inferTypeCore(d, false));
                    }
                    cur = (Expr) cur.o2;
                }
                try {
                    Expr[] fvarArr = fvarIdList.stream()
                        .map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr body = Reducer.instantiateRev(
                        cur, fvarArr.length, fvarArr, 0);
                    Expr r = inferTypeCore(body, inferOnly);
                    r = Reducer.cheapBetaReduce(r);
                    long[] fvarIds = new long[fvarIdList.size()];
                    for (int i = 0; i < fvarIds.length; i++)
                        fvarIds[i] = fvarIdList.get(i);
                    result = mkPi(fvarIds, fvarIds.length, r, false);
                } finally {
                    for (int i = fvarIdList.size() - 1; i >= 0; i--)
                        lctxRemove(fvarIdList.get(i));
                }
                break;
            }

            case Expr.FORALL: {
                // Matching Lean 4's infer_pi (type_checker.cpp:168-190)
                java.util.ArrayList<Long> fvarIdList = new java.util.ArrayList<>();
                java.util.ArrayList<Level> us = new java.util.ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.FORALL) {
                    Expr[] fvarArr = fvarIdList.isEmpty() ? new Expr[0] :
                        fvarIdList.stream().map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr d = Reducer.instantiateRev(
                        (Expr) cur.o1, fvarArr.length, fvarArr, 0);
                    Expr t1 = ensureSort(inferTypeCore(d, inferOnly));
                    us.add((Level) t1.o0);
                    long fvId = freshId();
                    Expr fv = Expr.fvar(fvId);
                    lctxAddLocal(fvId, cur.o0, d);
                    fvarIdList.add(fvId);
                    cur = (Expr) cur.o2;
                }
                try {
                    Expr[] fvarArr = fvarIdList.stream()
                        .map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr body = Reducer.instantiateRev(
                        cur, fvarArr.length, fvarArr, 0);
                    Expr s = ensureSort(inferTypeCore(body, inferOnly));
                    Level r = (Level) s.o0;
                    int i = fvarIdList.size();
                    while (i > 0) {
                        --i;
                        r = Level.imax(us.get(i), r);
                    }
                    result = Expr.sort(r, Level.hasParam(r));
                } finally {
                    for (int i = fvarIdList.size() - 1; i >= 0; i--)
                        lctxRemove(fvarIdList.get(i));
                }
                break;
            }

            case Expr.LET: {
                // Matching Lean 4's infer_let (type_checker.cpp:232-253)
                java.util.ArrayList<Long> fvarIdList = new java.util.ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.LET) {
                    Expr[] fvarArr = fvarIdList.isEmpty() ? new Expr[0] :
                        fvarIdList.stream().map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr type = Reducer.instantiateRev(
                        (Expr) cur.o1, fvarArr.length, fvarArr, 0);
                    Expr val = Reducer.instantiateRev(
                        (Expr) cur.o2, fvarArr.length, fvarArr, 0);
                    long fvId = freshId();
                    Expr fv = Expr.fvar(fvId);
                    lctxAddLet(fvId, cur.o0, type, val);
                    fvarIdList.add(fvId);
                    if (!inferOnly) {
                        ensureSort(inferTypeCore(type, false));
                        Expr valType = inferTypeCore(val, false);
                        if (!isDefEq(valType, type)) {
                            throw new RuntimeException("Type error: Let value type mismatch");
                        }
                    }
                    cur = (Expr) cur.o3;
                }
                try {
                    Expr[] fvarArr = fvarIdList.stream()
                        .map(id -> Expr.fvar(id)).toArray(Expr[]::new);
                    Expr body = Reducer.instantiateRev(
                        cur, fvarArr.length, fvarArr, 0);
                    Expr r = inferTypeCore(body, inferOnly);
                    r = Reducer.cheapBetaReduce(r);
                    long[] fvarIds = new long[fvarIdList.size()];
                    for (int i = 0; i < fvarIds.length; i++)
                        fvarIds[i] = fvarIdList.get(i);
                    result = mkPi(fvarIds, fvarIds.length, r, true);
                } finally {
                    for (int i = fvarIdList.size() - 1; i >= 0; i--)
                        lctxRemove(fvarIdList.get(i));
                }
                break;
            }

            case Expr.LIT_NAT:
                result = Expr.mkConst(Name.NAT, clojure.lang.PersistentVector.EMPTY, false);
                break;

            case Expr.LIT_STR:
                result = Expr.mkConst(Name.STRING, clojure.lang.PersistentVector.EMPTY, false);
                break;

            case Expr.MDATA:
                result = inferTypeCore((Expr) e.o1, inferOnly);
                break;

            case Expr.PROJ: {
                Expr structType = whnf(inferTypeCore((Expr) e.o1, inferOnly));
                Object[] fa = Reducer.getAppFnArgs(structType);
                Expr head = (Expr) fa[0];
                Expr[] typeArgs = (Expr[]) fa[1];
                if (head.tag != Expr.CONST) {
                    throw new RuntimeException("Type error: Projection target not an inductive");
                }
                ConstantInfo indCi = env.lookupOrThrow((Name) head.o0);
                if (!indCi.isInduct()) {
                    throw new RuntimeException("Type error: Projection target not an inductive");
                }
                if (indCi.ctors.length != 1) {
                    throw new RuntimeException("Type error: Projection on non-structure inductive");
                }
                Name ctorName = indCi.ctors[0];
                ConstantInfo ctorCi = env.lookupOrThrow(ctorName);
                HashMap<Object, Level> subst = new HashMap<>(ctorCi.levelParams.length * 2);
                Object[] headLevels = Reducer.constLevels(head);
                for (int i = 0; i < ctorCi.levelParams.length; i++) {
                    subst.put(ctorCi.levelParams[i], (Level) headLevels[i]);
                }
                Expr ctorType = Reducer.instantiateLevelParams(ctorCi.type, subst);
                int numParams = ctorCi.numParams;
                for (int i = 0; i < numParams && i < typeArgs.length && ctorType.tag == Expr.FORALL; i++) {
                    ctorType = Reducer.instantiate1((Expr) ctorType.o2, typeArgs[i]);
                }
                // Lean 4 type_checker.cpp:283-297: no data projection from Prop
                boolean isPropType = isProp(structType);
                int fieldIdx = (int) e.longVal;
                for (int i = 0; i < fieldIdx && ctorType.tag == Expr.FORALL; i++) {
                    // If structure is Prop and this intermediate field is NOT Prop
                    // and the body depends on it, reject (large elimination from Prop)
                    if (isPropType && ((Expr) ctorType.o2).bvarRange() > 0) {
                        if (!isProp((Expr) ctorType.o1))
                            throw new RuntimeException("Type error: data projection from Prop for " + e.o0 + " field " + i);
                    }
                    ctorType = Reducer.instantiate1((Expr) ctorType.o2, Expr.proj(e.o0, i, (Expr) e.o1));
                }
                if (ctorType.tag == Expr.FORALL) {
                    result = (Expr) ctorType.o1;
                    // Final field: also check Prop constraint
                    if (isPropType && !isProp(result))
                        throw new RuntimeException("Type error: data projection from Prop for " + e.o0 + " field " + fieldIdx);
                } else {
                    throw new RuntimeException("Type error: Not enough fields in constructor for proj idx " + fieldIdx);
                }
                break;
            }

            case Expr.FVAR: {
                Object[] decl = lctx.get(e.longVal);
                if (decl != null) {
                    result = (Expr) decl[2];
                } else {
                    throw new RuntimeException("Type error: Unknown free variable " + e.longVal);
                }
                break;
            }

            default:
                throw new RuntimeException("Type error: Unknown expression tag " + e.tag);
        }

        result = normalizeInferResult(result);
        identityCache.put(e, result);
        structuralCache.put(new LeanExprKey(e), result);
        return result;
    }

    private Expr ensureSort(Expr e) {
        Expr w = whnf(e);
        if (w.tag == Expr.SORT) return w;
        throw new RuntimeException("Type error: Expected a sort (Type/Prop)");
    }

    private Expr normalizeInferResult(Expr e) {
        return consumeTypeAnnotations(e);
    }

    static Expr consumeTypeAnnotations(Expr e) {
        Expr cur = e;
        while (cur.tag == Expr.APP) {
            Object[] fa = Reducer.getAppFnArgs(cur);
            Expr fn = (Expr) fa[0];
            Expr[] args = (Expr[]) fa[1];
            if (args.length == 1 && fn.tag == Expr.CONST) {
                Object nm = fn.o0;
                if (nm == Name.OUT_PARAM || nm == Name.SEMI_OUT_PARAM ||
                        Name.OUT_PARAM.equals(nm) || Name.SEMI_OUT_PARAM.equals(nm)) {
                    cur = args[0];
                    continue;
                }
            }
            break;
        }
        return cur;
    }

    Expr whnfExpr(Expr e) {
        return whnf(e);
    }

    Expr ensureSortExpr(Expr e) {
        return ensureSort(e);
    }

    /**
     * Ensure e is a Pi/forall type. Returns [name, domType, body, binderInfo].
     */
    private Expr[] ensurePi(Expr e) {
        Expr w = whnf(e);
        if (w.tag == Expr.FORALL) {
            return new Expr[]{
                (Expr) null,  // placeholder for name (not an Expr)
                (Expr) w.o1,  // domain type
                (Expr) w.o2,  // body
                (Expr) null   // placeholder for binder info
            };
        }
        throw new RuntimeException("Type error: Expected a function type (Pi/forall)");
    }

    /** Matching Lean's ensure_pi_core: return the Pi expression after whnf if needed. */
    private Expr ensurePiExpr(Expr e) {
        if (e.tag == Expr.FORALL) return e;
        Expr w = whnf(e);
        if (w.tag == Expr.FORALL) return w;
        throw new RuntimeException("Type error: Expected a function type (Pi/forall)");
    }

    // ============================================================
    // Definitional equality
    // ============================================================

    /**
     * Check definitional equality of two expressions.
     * Public entry point — records successful equivalences.
     */
    public boolean isDefEq(Expr t, Expr s) {
        // Lean only records successful equivalences at the public is_def_eq
        // wrapper. Internal is_def_eq_core calls must not pollute the global
        // equivalence manager, or later quick checks can succeed too early.
        boolean result = isDefEqCore(t, s);
        if (result) {
            emitEquivTrace("add_equiv.before", t, s);
            eqvManager.addEquiv(t, s);
            emitEquivTrace("add_equiv.after", t, s);
        }
        return result;
    }

    private boolean isDefEqCore(Expr t, Expr s) {
        boolean doEmit = traceWriter != null;
        isDefEqCalls++;
        if (isDefEqDepth < isDefEqDepthHist.length) isDefEqDepthHist[isDefEqDepth]++;
        // Capture a sample of expression shapes for diagnostics (only non-pointer-equal pairs)
        if (diagCaptures.size() < DIAG_CAPTURE_LIMIT && isDefEqDepth >= DIAG_CAPTURE_MIN_DEPTH && !t.isEqp(s)) {
            String ts = exprFingerprint(t, 6);
            String ss = exprFingerprint(s, 6);
            diagCaptures.add(new String[]{ts, ss, "d=" + isDefEqDepth});
        }
        if (t.isEqp(s)) {
            isDefEqQuickHits++;
            if (doEmit) {
                isDefEqDepth++;
                try {
                    if (TRACE_FULL && isDefEqDepth < traceLhsStack.length) {
                        traceLhsStack[isDefEqDepth] = t;
                        traceRhsStack[isDefEqDepth] = s;
                    }
                    emitTrace(exprFingerprint(t), exprFingerprint(s), true, "quick");
                } finally {
                    if (TRACE_FULL && isDefEqDepth < traceLhsStack.length) {
                        traceLhsStack[isDefEqDepth] = null;
                        traceRhsStack[isDefEqDepth] = null;
                    }
                    isDefEqDepth--;
                }
            }
            return true;
        }
        reducer.checkFuelPublic();
        isDefEqDepth++;
        try {
            return isDefEqCoreImpl(t, s);
        } finally {
            isDefEqDepth--;
        }
    }

    /**
     * Quick definitional equality check matching Lean 4's quick_is_def_eq.
     * Handles "easy cases" without WHNF reduction.
     * Returns: 1=equal, -1=not equal, 0=unknown.
     */
    private int quickIsDefEq(Expr t, Expr s) {
        return quickIsDefEq(t, s, true);
    }

    private int quickIsDefEq(Expr t, Expr s, boolean useHash) {
        // Lean's quick_is_def_eq calls is_equiv(t, s, use_hash) which does
        // deep structural comparison with union-find merging.
        if (eqvManager.isEquiv(t, s, useHash)) return 1;
        if (t.tag == s.tag) {
            switch (t.tag) {
                case Expr.LAM: case Expr.FORALL:
                    return isDefEqBinding(t, s) ? 1 : -1;
                case Expr.SORT:
                    return Level.eq((Level) t.o0, (Level) s.o0) ? 1 : -1;
                case Expr.MDATA:
                    return isDefEq((Expr) t.o1, (Expr) s.o1) ? 1 : -1;
                case Expr.LIT_NAT:
                    return ((BigInteger) t.o0).equals((BigInteger) s.o0) ? 1 : -1;
                case Expr.LIT_STR:
                    return t.o0.equals(s.o0) ? 1 : -1;
                default:
                    break;
            }
        }
        return 0;
    }

    /**
     * Binding (Lambda/Pi) definitional equality.
     * Matching Lean 4's is_def_eq_binding (type_checker.cpp:726-753).
     * Loops through chains of same-kind binders, skipping domain isDefEq
     * when domains are structurally identical, and only creates FVars when
     * the body actually uses the bound variable.
     */
    private boolean isDefEqBinding(Expr t, Expr s) {
        byte k = t.tag;
        java.util.ArrayList<Long> addedFvars = new java.util.ArrayList<>();
        java.util.ArrayList<Expr> substList = new java.util.ArrayList<>();
        try {
            do {
                Expr domT = (Expr) t.o1;
                Expr domS = (Expr) s.o1;
                Expr varSType = null;
                // Lean uses pointer equality (is_eqp) here.
                // We use isEqp which checks Java identity OR matching storeId.
                emitBindingDomainTrace(t, s, domT, domS);
                if (!domT.isEqp(domS)) {
                    varSType = instantiateRevList(domS, substList);
                    Expr varTType = instantiateRevList(domT, substList);
                    if (!isDefEq(varTType, varSType))
                        return false;
                }
                Expr bodyT = (Expr) t.o2;
                Expr bodyS = (Expr) s.o2;
                if (bodyT.bvarRange() > 0 || bodyS.bvarRange() > 0) {
                    // Free variable is used inside t or s — create FVar
                    if (varSType == null)
                        varSType = instantiateRevList(domS, substList);
                    long fvId = freshId();
                    Expr fv = Expr.fvar(fvId);
                    lctxAddLocal(fvId, null, varSType);
                    addedFvars.add(fvId);
                    substList.add(fv);
                } else {
                    // Body doesn't use the variable — use don't-care placeholder
                    substList.add(Expr.sort(Level.ZERO_LEVEL, false)); // placeholder, won't be substituted
                }
                t = bodyT;
                s = bodyS;
            } while (t.tag == k && s.tag == k);
            return isDefEq(instantiateRevList(t, substList),
                           instantiateRevList(s, substList));
        } finally {
            for (Long fvId : addedFvars) {
                lctxRemove(fvId);
            }
        }
    }

    /** Helper: instantiateRev with ArrayList. */
    private static Expr instantiateRevList(Expr e, java.util.ArrayList<Expr> subst) {
        int n = subst.size();
        if (n == 0 || e.bvarRange() == 0) return e;
        Expr[] arr = subst.toArray(new Expr[n]);
        return Reducer.instantiateRev(e, n, arr, 0);
    }

    private boolean isDefEqCoreImpl(Expr t, Expr s) {
        boolean doTrace = tracing && isDefEqDepth >= traceMinDepth;
        boolean doEmit = traceWriter != null;
        boolean doStepDiag = isDefEqDepth >= STEP_DIAG_DEPTH;
        if (TRACE_FULL && isDefEqDepth < traceLhsStack.length) {
            traceLhsStack[isDefEqDepth] = t;
            traceRhsStack[isDefEqDepth] = s;
        }
        String lFp = null, rFp = null;
        if (doEmit) {
            lFp = exprFingerprint(t);
            rFp = exprFingerprint(s);
        }
        if (isDefEqDepth > MAX_ISDEFEQ_DEPTH) {
            throw new RuntimeException("isDefEq recursion depth exceeded (" + MAX_ISDEFEQ_DEPTH + ")");
        }
        if (doTrace) {
            trace("isDefEq d=" + isDefEqDepth + " " + exprSummary(t, 3) + " =?= " + exprSummary(s, 3));
        }
        if (doStepDiag) stepDiagTotal++;

        // Step 1: Quick check (Lean 4 line 1061)
        {
            int q = quickIsDefEq(t, s);
            if (q != 0) {
                boolean r = q == 1;
                if (doEmit) emitTrace(lFp, rFp, r, "quick");
                if (doStepDiag) stepDiagQuick++;
                return r;
            }
        }

        // Step 1b: Bool.true optimization for `decide` tactic (Lean 4 lines 1064-1072)
        if ((!t.hasFVar() || eagerReduce) && s.tag == Expr.CONST && s.o0 == Name.BOOL_TRUE) {
            Expr tw = reducer.whnf(t);
            if (tw.tag == Expr.CONST && tw.o0 == Name.BOOL_TRUE) {
                if (doEmit) emitTrace(lFp, rFp, true, "decide");
                return true;
            }
        }

        // Step 2: whnf_core with Lean 4 flags (cheapRec=false, cheapProj=true).
        // deepReIntern canonicalizes the result bottom-up through the intern table,
        // matching Lean 4's global hash-consing: structurally equal trees from
        // different reduction paths become pointer-equal → quick identity check fires.
        Expr tnRaw = reducer.whnfCore(t, false, true);
        Expr snRaw = reducer.whnfCore(s, false, true);
        boolean whnfChanged = !tnRaw.isEqp(t) || !snRaw.isEqp(s);
        Expr tn = Expr.deepReIntern(tnRaw);
        Expr sn = Expr.deepReIntern(snRaw);

        // Quick check after whnf_core (Lean 4 lines 1116-1124)
        // Note: Lean uses use_hash=false (default) for the second quick check
        if (whnfChanged) {
            emitEquivTrace("quick_whnfcore.before", tn, sn);
            int q = quickIsDefEq(tn, sn, false);
            emitEquivTrace("quick_whnfcore.after." + q, tn, sn);
            if (q != 0) {
                boolean r = q == 1;
                if (doTrace) trace("=> quickEq after whnfCore");
                if (doEmit) emitTrace(lFp, rFp, r, "quick_whnfcore");
                return r;
            }
        }
        if (!whnfChanged
            && (tn.tag == Expr.PROJ || sn.tag == Expr.PROJ)
            && eqvManager.isKnownEquiv(tn, sn)
            && !hasZeroFieldStructureType(tn)
            && !hasZeroFieldStructureType(sn)) {
            // Lean can observe a pointer change from whnf_core around projection
            // terms and then reuse an existing equivalence-manager proof in the
            // second quick check. Our stronger re-interning/pointer preservation
            // can hide that change, so keep the same phase for projection pairs
            // whose equality has already been established by the public
            // isDefEq/addEquiv path. Do not do this for unit-like result types:
            // Lean keeps exploring those until the dedicated unit_like rule.
            if (doEmit) emitTrace(lFp, rFp, true, "quick_whnfcore");
            return true;
        }
        if (doTrace) {
            if (whnfChanged)
                trace("  whnfCore: " + exprSummary(tn, 3) + " =?= " + exprSummary(sn, 3));
        }

        // Step 3: Proof irrelevance (before lazy delta, matching Lean 4)
        {
            int piResult = proofIrrelevant(tn, sn);
            if (piResult == 1) {
                if (doTrace) trace("=> proofIrrel");
                if (doEmit) emitTrace(lFp, rFp, true, "proof_irrel");
                if (doStepDiag) stepDiagProofIrrel++;
                return true;
            }
            if (piResult == -1) {
                if (doTrace) trace("=> proofIrrel FAIL");
                if (doEmit) emitTrace(lFp, rFp, false, "proof_irrel");
                if (doStepDiag) stepDiagProofIrrel++;
                return false;
            }
        }

        // Step 4: Lazy delta reduction
        int deltaResult = lazyDeltaReduction(tn, sn);
        if (deltaResult == 1) {
            if (doTrace) trace("=> lazyDelta EQ");
            if (doEmit) emitTrace(lFp, rFp, true, "lazy_delta");
            if (doStepDiag) stepDiagLazyDelta++;
            return true;
        }
        if (deltaResult == -1) {
            if (doTrace) trace("=> lazyDelta NEQ");
            if (doEmit) emitTrace(lFp, rFp, false, "lazy_delta");
            if (doStepDiag) stepDiagLazyDelta++;
            return false;
        }

        // After lazy delta, tn and sn are stored in deltaHolder
        tn = deltaHolder[0];
        sn = deltaHolder[1];

        // Step 5: Same-head constants/fvars check
        if (tn.tag == sn.tag) {
            switch (tn.tag) {
                case Expr.CONST:
                    if (tn.o0.equals(sn.o0)) {
                        Object[] tl = Reducer.constLevels(tn);
                        Object[] sl = Reducer.constLevels(sn);
                        if (tl.length == sl.length) {
                            boolean allEq = true;
                            for (int i = 0; i < tl.length; i++) {
                                if (!Level.eq((Level) tl[i], (Level) sl[i])) { allEq = false; break; }
                            }
                            if (allEq) {
                                if (doEmit) emitTrace(lFp, rFp, true, "const_eq");
                                return true;
                            }
                        }
                    }
                    break;
                case Expr.FVAR:
                    if (tn.longVal == sn.longVal) {
                        if (doEmit) emitTrace(lFp, rFp, true, "fvar_eq");
                        return true;
                    }
                    break;
            }
        }

        // Step 5b: Projection structure check
        if (tn.tag == Expr.PROJ && sn.tag == Expr.PROJ &&
            tn.longVal == sn.longVal) {
            if (lazyDeltaProjReduction((Expr) tn.o1, (Expr) sn.o1, (int) tn.longVal)) {
                if (doEmit) emitTrace(lFp, rFp, true, "proj_delta");
                return true;
            }
        }

        // Step 6: Second whnf_core pass with full flags
        {
            Expr tn2Raw = reducer.whnfCore(tn, false, false);
            Expr sn2Raw = reducer.whnfCore(sn, false, false);
            boolean whnf2Changed = !tn2Raw.isEqp(tn) || !sn2Raw.isEqp(sn);
            Expr tn2 = Expr.deepReIntern(tn2Raw);
            Expr sn2 = Expr.deepReIntern(sn2Raw);
            if (whnf2Changed) {
                emitPhasePairStats("step6.whnfcore2.stats", tn2, sn2);
                emitPhaseTypes("step6.whnfcore2.types", tn2, sn2);
                boolean r = isDefEqCore(tn2, sn2);
                if (doEmit) emitTrace(lFp, rFp, r, "whnfcore2");
                if (doStepDiag) stepDiagWhnfCore2++;
                return r;
            }
        }

        // Step 7: Sort comparison
        if (tn.tag == Expr.SORT && sn.tag == Expr.SORT) {
            boolean r = Level.eq((Level) tn.o0, (Level) sn.o0);
            if (doEmit) emitTrace(lFp, rFp, r, "sort_eq");
            if (doStepDiag) stepDiagApp++;  // count in "app" bucket for sorts
            return r;
        }

        // Step 8: App congruence
        if (tn.tag == Expr.APP && sn.tag == Expr.APP) {
            if (isDefEqApp(tn, sn)) {
                if (doEmit) emitTrace(lFp, rFp, true, "app");
                if (doStepDiag) stepDiagApp++;
                return true;
            }
        }

        // Step 9: Lambda/forall congruence
        if ((tn.tag == Expr.LAM && sn.tag == Expr.LAM) ||
            (tn.tag == Expr.FORALL && sn.tag == Expr.FORALL)) {
            boolean r = isDefEqBinding(tn, sn);
            if (doEmit) emitTrace(lFp, rFp, r, "binding");
            if (doStepDiag) stepDiagBinding++;
            return r;
        }

        // Step 10: Eta expansion
        if (tryEta(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta"); if (doStepDiag) stepDiagEta++; return true; }
        if (tryEta(sn, tn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta"); if (doStepDiag) stepDiagEta++; return true; }

        // Step 11: Eta struct expansion
        if (tryEtaStruct(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta_struct"); if (doStepDiag) stepDiagEta++; return true; }

        // Step 11b: String literal expansion
        {
            int r = tryStringLitExpansion(tn, sn);
            if (r == 1) { if (doEmit) emitTrace(lFp, rFp, true, "string_lit"); if (doStepDiag) stepDiagApp++; return true; }
            if (r == -1) { if (doEmit) emitTrace(lFp, rFp, false, "string_lit"); if (doStepDiag) stepDiagFail++; return false; }
        }

        // Step 12: Unit-like types
        if (isDefEqUnitLike(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "unit_like"); if (doStepDiag) stepDiagUnit++; return true; }

        // Step 13: Proof irrelevance (after full reduction — extra, not in Lean)
        {
            int piResult2 = proofIrrelevant(tn, sn);
            if (piResult2 == 1) {
                if (doTrace) trace("=> proofIrrel(late)");
                if (doEmit) emitTrace(lFp, rFp, true, "proof_irrel2");
                if (doStepDiag) stepDiagProofIrrel++;
                return true;
            }
            if (piResult2 == -1) {
                if (doTrace) trace("=> proofIrrel(late) FAIL");
                if (doEmit) emitTrace(lFp, rFp, false, "proof_irrel2");
                if (doStepDiag) stepDiagProofIrrel++;
                return false;
            }
        }

        if (doTrace) {
            trace("=> FAIL d=" + isDefEqDepth + " " + exprSummary(tn, 4) + " =?= " + exprSummary(sn, 4));
        }
        if (doEmit) emitTrace(lFp, rFp, false, "fail");
        if (doStepDiag) stepDiagFail++;
        return false;
    }

    // Holder for lazy delta reduction output
    private final Expr[] deltaHolder = new Expr[2];

    /**
     * Lazy delta reduction. Returns: 1=equal, -1=not equal, 0=unknown.
     * Updates deltaHolder[0] and deltaHolder[1] with the final tn, sn.
     */
    private int lazyDeltaReduction(Expr tn, Expr sn) {
        deltaHolder[0] = tn;
        deltaHolder[1] = sn;

        for (int iter = 0; iter < 10000; iter++) {
            tn = deltaHolder[0];
            sn = deltaHolder[1];
            emitDeltaTrace("start", tn, sn);

            // Nat offset check
            int offsetResult = isDefEqOffset(tn, sn);
            if (offsetResult != 0) {
                emitDeltaTrace("offset", tn, sn);
                return offsetResult;
            }

            // Nat builtin reduction (matching Lean 4's lazy_delta_reduction lines 980-986)
            // Lean 4 delegates to is_def_eq_core on the reduced result.
            // In eagerReduce mode, also fire when terms have fvars (Lean 4 line 980)
            if ((!tn.hasFVar() && !sn.hasFVar()) || eagerReduce) {
                Expr natTn = reducer.tryReduceNatExpr(tn);
                if (natTn != null) {
                    emitDeltaTrace("reduceNat.left", natTn, sn);
                    return isDefEqCore(natTn, sn) ? 1 : -1;
                }
                Expr natSn = reducer.tryReduceNatExpr(sn);
                if (natSn != null) {
                    emitDeltaTrace("reduceNat.right", tn, natSn);
                    return isDefEqCore(tn, natSn) ? 1 : -1;
                }
                // Try Int reduction (native optimization)
                Object[] tnFA0 = Reducer.getAppFnArgs(tn);
                Expr intTn = reducer.tryReduceInt((Expr) tnFA0[0], (Expr[]) tnFA0[1]);
                if (intTn != null) {
                    emitDeltaTrace("reduceInt.left", intTn, sn);
                    return isDefEqCore(intTn, sn) ? 1 : -1;
                }
                Object[] snFA0 = Reducer.getAppFnArgs(sn);
                Expr intSn = reducer.tryReduceInt((Expr) snFA0[0], (Expr[]) snFA0[1]);
                if (intSn != null) {
                    emitDeltaTrace("reduceInt.right", tn, intSn);
                    return isDefEqCore(tn, intSn) ? 1 : -1;
                }
            }

            Object[] tnFA = Reducer.getAppFnArgs(tn);
            Object[] snFA = Reducer.getAppFnArgs(sn);
            Expr tnHead = (Expr) tnFA[0];
            Expr snHead = (Expr) snFA[0];

            // Is either side a delta (unfoldable definition)?
            ConstantInfo dtInfo = deltaInfo(tnHead);
            ConstantInfo dsInfo = deltaInfo(snHead);
            boolean dtHasDelta = dtInfo != null;
            boolean dsHasDelta = dsInfo != null;

            if (!dtHasDelta && !dsHasDelta) {
                emitDeltaTrace("unknown.noDelta", tn, sn);
                return 0; // Neither side can be unfolded
            }

            if (dtHasDelta && !dsHasDelta) {
                // Only left side is a definition — but first try to unfold projection app on right
                // (Lean 4 lines 900-904: try_unfold_proj_app optimization)
                Expr snNew = tryUnfoldProjApp(sn);
                if (snNew != null) {
                    sn = snNew;
                    emitDeltaTrace("proj.right", tn, sn);
                } else {
                    Expr unfolded = reducer.tryUnfoldDef(tnHead);
                    if (unfolded == null) return 0;
                    tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                    emitDeltaTrace("unfold.left", tn, sn);
                }
            } else if (!dtHasDelta && dsHasDelta) {
                // Only right side is a definition — but first try to unfold projection app on left
                // (Lean 4 lines 907-911: try_unfold_proj_app optimization)
                Expr tnNew = tryUnfoldProjApp(tn);
                if (tnNew != null) {
                    tn = tnNew;
                    emitDeltaTrace("proj.left", tn, sn);
                } else {
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return 0;
                    sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                    emitDeltaTrace("unfold.right", tn, sn);
                }
            } else {
                // Both sides are definitions — use hints to decide
                int tHints = dtInfo.getHints();
                int sHints = dsInfo.getHints();
                int cmp = compareHints(tHints, sHints);

                if (cmp < 0) {
                    // Unfold left (higher height / more complex)
                    Expr unfolded = reducer.tryUnfoldDef(tnHead);
                    if (unfolded == null) return 0;
                    tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                    emitDeltaTrace("unfold.left", tn, sn);
                } else if (cmp > 0) {
                    // Unfold right
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return 0;
                    sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                    emitDeltaTrace("unfold.right", tn, sn);
                } else {
                    // Same hint level — Lean takes this shortcut when is_delta
                    // resolves both sides to the same declaration object, even if
                    // the head constants carry syntactically different levels.
                    if (tn.tag == Expr.APP && sn.tag == Expr.APP &&
                        dtInfo == dsInfo && tHints > 0) {
                        emitPhase("lazyDelta.sameDefArgs");
                        // Same definition with Regular hints — identity-based failure cache
                        if (!failedBefore(tn, sn)) {
                            emitPhaseTypes("lazyDelta.sameDefArgs.types", tn, sn);
                            // Try comparing arguments
                            Object[] tLvls = Reducer.constLevels(tnHead);
                            Object[] sLvls = Reducer.constLevels(snHead);
                            if (levelsEq(tLvls, sLvls) && isDefEqArgs(tn, sn)) {
                                deltaHolder[0] = tn;
                                deltaHolder[1] = sn;
                                return 1; // Equal via argument comparison
                            }
                            cacheFailure(tn, sn);
                        }
                    }
                    emitPhase("lazyDelta.unfoldBoth");
                    // Unfold both
                    Expr unfoldedT = reducer.tryUnfoldDef(tnHead);
                    Expr unfoldedS = reducer.tryUnfoldDef(snHead);
                    if (unfoldedT == null && unfoldedS == null) return 0;
                    if (unfoldedT != null) {
                        tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true));
                    }
                    if (unfoldedS != null) {
                        sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true));
                    }
                    emitDeltaTrace("unfold.both", tn, sn);
                    emitPhasePairStats("lazyDelta.unfoldBoth.stats", tn, sn);
                }
            }

            // Quick check after update (Lean 4 line 996: quick_is_def_eq, use_hash=false default)
            deltaHolder[0] = tn;
            deltaHolder[1] = sn;
            {
                int q = quickIsDefEq(tn, sn, false);
                if (q != 0) emitPhase("lazyDelta.postQuick.hit");
                else emitPhase("lazyDelta.postQuick.miss");
                emitPhasePairStats("lazyDelta.postQuick.stats", tn, sn);
                emitDeltaTrace(q == 1 ? "quick.eq" : (q == -1 ? "quick.diff" : "quick.unknown"), tn, sn);
                if (q == 1) return 1;   // DefEqual
                if (q == -1) return -1; // DefDiff
            }
        }

        return 0; // Iteration limit
    }

    /**
     * Nat offset check matching Lean 4's is_def_eq_offset (type_checker.cpp:963-972).
     * Lean 4's is_nat_succ treats lit-nat(n) where n>0 as Nat.succ(lit-nat(n-1)).
     * This allows comparing Nat.succ(OfNat.ofNat...) =?= lit-nat(2) by peeling
     * one succ from each side and recursively calling isDefEqCore.
     * Returns: 1=equal, -1=not equal, 0=unknown.
     */
    private int isDefEqOffset(Expr t, Expr s) {
        // Fast path: strip all Nat.succ layers from both sides and check if
        // both bottom out at lit-nat or Nat.zero (avoids recursive depth cost)
        int tOffset = 0, sOffset = 0;
        Expr tInner = t, sInner = s;
        while (tInner.tag == Expr.APP && ((Expr) tInner.o0).tag == Expr.CONST &&
               ((Expr) tInner.o0).o0 == Name.NAT_SUCC) {
            tOffset++;
            tInner = (Expr) tInner.o1;
        }
        while (sInner.tag == Expr.APP && ((Expr) sInner.o0).tag == Expr.CONST &&
               ((Expr) sInner.o0).o0 == Name.NAT_SUCC) {
            sOffset++;
            sInner = (Expr) sInner.o1;
        }
        // Both bottomed out at lit-nat — compare total values iteratively
        if (tInner.tag == Expr.LIT_NAT && sInner.tag == Expr.LIT_NAT) {
            BigInteger tv = ((BigInteger) tInner.o0).add(BigInteger.valueOf(tOffset));
            BigInteger sv = ((BigInteger) sInner.o0).add(BigInteger.valueOf(sOffset));
            return tv.equals(sv) ? 1 : -1;
        }
        // Both Nat.zero — compare offsets
        if (isNatZero(tInner) && isNatZero(sInner)) {
            return tOffset == sOffset ? 1 : -1;
        }

        // Lean 4 recursive approach: if both sides have a predecessor
        // (Nat.succ(x) or lit-nat(n>0)), peel one layer and call isDefEqCore
        // which triggers full machinery including lazy delta on inner exprs.
        Expr predT = natPred(t);
        Expr predS = natPred(s);
        if (predT != null && predS != null) {
            return isDefEqCore(predT, predS) ? 1 : -1;
        }

        // Both are Nat.zero (including lit-nat(0))
        if (isNatZero(t) && isNatZero(s)) return 1;

        return 0;
    }

    /** Lean 4's is_nat_succ: extract predecessor of a nat expression.
     *  - lit-nat(n) where n>0 → lit-nat(n-1)
     *  - Nat.succ(x) → x
     *  - otherwise → null
     */
    private static Expr natPred(Expr e) {
        if (e.tag == Expr.LIT_NAT) {
            BigInteger val = (BigInteger) e.o0;
            if (val.signum() > 0) {
                return Expr.litNat(val.subtract(BigInteger.ONE));
            }
            return null;
        }
        if (e.tag == Expr.APP && ((Expr) e.o0).tag == Expr.CONST &&
            ((Expr) e.o0).o0 == Name.NAT_SUCC) {
            return (Expr) e.o1;
        }
        return null;
    }

    private static boolean isNatZero(Expr e) {
        return (e.tag == Expr.CONST && e.o0 == Name.NAT_ZERO) ||
               (e.tag == Expr.LIT_NAT && ((BigInteger) e.o0).signum() == 0);
    }

    /**
     * String literal expansion matching Lean 4's try_string_lit_expansion.
     * If one side is a string literal and the other is String.mk/String.ofList applied to a list,
     * expand the literal to constructor form and compare.
     * Returns: 1=equal, -1=not equal, 0=unknown.
     */
    private int tryStringLitExpansion(Expr t, Expr s) {
        int r = tryStringLitExpansionCore(t, s);
        if (r != 0) return r;
        return tryStringLitExpansionCore(s, t);
    }

    private int tryStringLitExpansionCore(Expr t, Expr s) {
        // If t is a string literal and s is not, expand t to constructor form
        if (t.tag != Expr.LIT_STR) return 0;
        if (s.tag == Expr.LIT_STR) return 0; // Both lit-str, already compared structurally

        Expr expanded = stringLitToConstructor(t);
        return isDefEqCore(expanded, s) ? 1 : -1;
    }

    /**
     * Convert string literal to constructor form: String.mk [Char.ofNat c1, ..., Char.ofNat cn]
     * Matching Lean 4's string_lit_to_constructor (inductive.cpp:1200-1212).
     */
    private static Expr stringLitToConstructor(Expr e) {
        String str = (String) e.o0;
        // Build List Char from right to left
        Level zeroLevel = Level.ZERO_LEVEL;
        Expr charType = Expr.mkConst(Name.CHAR, new Level[0], false);
        Expr listNilChar = Expr.app(
            Expr.mkConst(Name.LIST_NIL, new Level[]{zeroLevel}, false),
            charType);
        Expr listConsChar = Expr.app(
            Expr.mkConst(Name.LIST_CONS, new Level[]{zeroLevel}, false),
            charType);
        Expr charOfNat = Expr.mkConst(Name.CHAR_OF_NAT, new Level[0], false);

        // UTF-8 decode to codepoints
        int[] codepoints = str.codePoints().toArray();

        Expr r = listNilChar;
        for (int i = codepoints.length - 1; i >= 0; i--) {
            Expr ch = Expr.app(charOfNat, Expr.litNat(BigInteger.valueOf(codepoints[i])));
            r = Expr.app(Expr.app(listConsChar, ch), r);
        }
        // Lean 4's g_string_mk is actually String.ofList (despite the variable name)
        return Expr.app(Expr.mkConst(Name.STRING_OF_LIST, new Level[0], false), r);
    }

    /**
     * Lean 4's try_unfold_proj_app: if e is of the form proj(S, i, ...) args...,
     * try to reduce it via whnf_core. Returns the reduced expression or null.
     * This avoids expensive delta-unfolding of the other side when a projection
     * can be reduced directly.
     */
    private Expr tryUnfoldProjApp(Expr e) {
        Object[] fa = Reducer.getAppFnArgs(e);
        Expr fn = (Expr) fa[0];
        if (fn.tag != Expr.PROJ) return null;
        Expr eNew = reducer.whnfCore(e);
        return !LeanExprKey.exprEquals(eNew, e) ? eNew : null;
    }

    /** Return the delta declaration for a head constant, if it is unfoldable. */
    private ConstantInfo deltaInfo(Expr head) {
        if (head.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookup((Name) head.o0);
        return ci != null && ci.getValue() != null ? ci : null;
    }

    /** Check if head constant is a delta (unfoldable definition). */
    private boolean isDelta(Expr head) {
        return deltaInfo(head) != null;
    }

    /** Get reducibility hints for a head constant. Returns -1 for opaque, 0 for abbrev, >0 for regular. */
    private int getHints(Expr head) {
        if (head.tag != Expr.CONST) return ConstantInfo.HINTS_OPAQUE;
        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null) return ConstantInfo.HINTS_OPAQUE;
        return ci.getHints();
    }

    /**
     * Compare hints for lazy delta. Returns:
     * < 0: unfold t (t has higher height or should be unfolded first)
     * > 0: unfold s
     * = 0: unfold both
     */
    private static int compareHints(int t, int s) {
        // Both opaque: can't unfold
        if (t == ConstantInfo.HINTS_OPAQUE && s == ConstantInfo.HINTS_OPAQUE) return 0;
        // One opaque: unfold the non-opaque
        if (t == ConstantInfo.HINTS_OPAQUE) return 1;
        if (s == ConstantInfo.HINTS_OPAQUE) return -1;
        // Abbrev (0) vs regular (>0): unfold abbrev first
        if (t == ConstantInfo.HINTS_ABBREV && s > 0) return -1;
        if (s == ConstantInfo.HINTS_ABBREV && t > 0) return 1;
        // Both abbrev: unfold both
        if (t == ConstantInfo.HINTS_ABBREV && s == ConstantInfo.HINTS_ABBREV) return 0;
        // Both regular: unfold the one with higher height (defined later)
        if (t > 0 && s > 0) {
            if (t > s) return -1;  // t is higher, unfold t
            if (t < s) return 1;   // s is higher, unfold s
            return 0;              // same height, unfold both
        }
        return 0;
    }

    private static boolean levelsEq(Object[] a, Object[] b) {
        if (a.length != b.length) return false;
        for (int i = 0; i < a.length; i++) {
            if (!Level.eq((Level) a[i], (Level) b[i])) return false;
        }
        return true;
    }

    private boolean failedBeforeIdentity(Expr t, Expr s) {
        IdentityHashMap<Expr, Boolean> inner = failureIdentityCache.get(t);
        return inner != null && Boolean.TRUE.equals(inner.get(s));
    }

    private boolean failedBeforeStructural(Expr t, Expr s) {
        HashMap<LeanExprKey, Boolean> inner = failureStructuralCache.get(new LeanExprKey(t));
        return inner != null && Boolean.TRUE.equals(inner.get(new LeanExprKey(s)));
    }

    private boolean failedBefore(Expr t, Expr s) {
        int cmp = Integer.compareUnsigned(LeanExprKey.hashExpr(t), LeanExprKey.hashExpr(s));
        if (cmp < 0) {
            return failedBeforeIdentity(t, s) || failedBeforeStructural(t, s);
        } else if (cmp > 0) {
            return failedBeforeIdentity(s, t) || failedBeforeStructural(s, t);
        } else {
            return failedBeforeIdentity(t, s) || failedBeforeIdentity(s, t)
                || failedBeforeStructural(t, s) || failedBeforeStructural(s, t);
        }
    }

    private void cacheFailureOrdered(Expr t, Expr s) {
        IdentityHashMap<Expr, Boolean> identityInner = failureIdentityCache.get(t);
        if (identityInner == null) {
            identityInner = new IdentityHashMap<>(4);
            failureIdentityCache.put(t, identityInner);
        }
        identityInner.put(s, Boolean.TRUE);

        LeanExprKey tKey = new LeanExprKey(t);
        HashMap<LeanExprKey, Boolean> structuralInner = failureStructuralCache.get(tKey);
        if (structuralInner == null) {
            structuralInner = new HashMap<>(4);
            failureStructuralCache.put(tKey, structuralInner);
        }
        structuralInner.put(new LeanExprKey(s), Boolean.TRUE);
    }

    private void cacheFailure(Expr t, Expr s) {
        if (Integer.compareUnsigned(LeanExprKey.hashExpr(t), LeanExprKey.hashExpr(s)) <= 0) {
            cacheFailureOrdered(t, s);
        } else {
            cacheFailureOrdered(s, t);
        }
    }

    /**
     * Lazy delta projection reduction (Lean 4's lazy_delta_proj_reduction).
     * When both sides are projections with the same index, try lazy delta
     * on the struct arguments, then fall back to reduce_proj_core.
     */
    private boolean lazyDeltaProjReduction(Expr tc, Expr sc, int idx) {
        // Run lazy delta reduction steps on the struct expressions
        Expr[] holder = new Expr[]{tc, sc};
        for (int iter = 0; iter < 10000; iter++) {
            tc = holder[0];
            sc = holder[1];
            int step = lazyDeltaReductionStep(tc, sc, holder);
            if (step == 1) return true;   // DefEqual
            if (step == 0 || step == -1) {
                // DefUnknown or DefDiff — try reducing projections
                tc = holder[0];
                sc = holder[1];
                Expr tProj = reduceProjCore(tc, idx);
                if (tProj != null) {
                    Expr sProj = reduceProjCore(sc, idx);
                    if (sProj != null) {
                        return isDefEqCore(tProj, sProj);
                    }
                }
                return isDefEqCore(tc, sc);
            }
            // step == 2 means Continue — loop
        }
        return false;
    }

    /**
     * Single step of lazy delta reduction (Lean 4's lazy_delta_reduction_step).
     * Returns: 1=DefEqual, -1=DefDiff, 0=DefUnknown, 2=Continue.
     * Updates holder[0] and holder[1] with updated tn, sn.
     */
    private int lazyDeltaReductionStep(Expr tn, Expr sn, Expr[] holder) {
        Object[] tnFA = Reducer.getAppFnArgs(tn);
        Object[] snFA = Reducer.getAppFnArgs(sn);
        Expr tnHead = (Expr) tnFA[0];
        Expr snHead = (Expr) snFA[0];

        ConstantInfo dtInfo = deltaInfo(tnHead);
        ConstantInfo dsInfo = deltaInfo(snHead);
        boolean dtHasDelta = dtInfo != null;
        boolean dsHasDelta = dsInfo != null;

        if (!dtHasDelta && !dsHasDelta) return 0; // DefUnknown

        if (dtHasDelta && !dsHasDelta) {
            // Lean: try to unfold projection app on the non-delta side first
            Expr snNew = tryUnfoldProjApp(sn);
            if (snNew != null) {
                sn = snNew;
                holder[1] = sn;
            } else {
                Expr unfolded = reducer.tryUnfoldDef(tnHead);
                if (unfolded == null) return 0;
                tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                holder[0] = tn;
            }
        } else if (!dtHasDelta && dsHasDelta) {
            // Lean: try to unfold projection app on the non-delta side first
            Expr tnNew = tryUnfoldProjApp(tn);
            if (tnNew != null) {
                tn = tnNew;
                holder[0] = tn;
            } else {
                Expr unfolded = reducer.tryUnfoldDef(snHead);
                if (unfolded == null) return 0;
                sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                holder[1] = sn;
            }
        } else {
            // Both delta
            int tHints = dtInfo.getHints();
            int sHints = dsInfo.getHints();
            int cmp = compareHints(tHints, sHints);

            if (cmp < 0) {
                Expr unfolded = reducer.tryUnfoldDef(tnHead);
                if (unfolded == null) return 0;
                tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                holder[0] = tn;
            } else if (cmp > 0) {
                Expr unfolded = reducer.tryUnfoldDef(snHead);
                if (unfolded == null) return 0;
                sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                holder[1] = sn;
            } else {
                // Same hint level — Lean takes this shortcut when is_delta
                // resolves both sides to the same declaration object, even if
                // the head constants carry syntactically different levels.
                Expr[] tnArgs = (Expr[]) tnFA[1];
                Expr[] snArgs = (Expr[]) snFA[1];
                if (dtInfo == dsInfo
                    && tnArgs.length == snArgs.length
                    && tHints > 0) { // regular hints (positive = regular in our encoding)
                    if (!failedBefore(tn, sn)) {
                        if (levelsEq(Reducer.constLevels(tnHead), Reducer.constLevels(snHead))
                            && isDefEqArgs(tn, sn)) {
                            holder[0] = tn;
                            holder[1] = sn;
                            return 1; // DefEqual via argument comparison
                        }
                        cacheFailure(tn, sn);
                    }
                }
                // Unfold both
                Expr unfoldedT = reducer.tryUnfoldDef(tnHead);
                Expr unfoldedS = reducer.tryUnfoldDef(snHead);
                if (unfoldedT == null && unfoldedS == null) return 0;
                if (unfoldedT != null) {
                    tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true));
                    holder[0] = tn;
                }
                if (unfoldedS != null) {
                    sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true));
                    holder[1] = sn;
                }
            }
        }
        // Quick check after reduction (matching Lean's quick_is_def_eq, use_hash=false default)
        {
            int q = quickIsDefEq(tn, sn, false);
            if (q == 1) return 1;
            if (q == -1) return -1;
        }
        holder[0] = tn;
        holder[1] = sn;
        return 2; // Continue
    }

    /**
     * Reduce a projection structurally (Lean 4's reduce_proj_core).
     * Given a constructor application, extract the field at index idx.
     * Does NOT call whnf — only works if the expression is already a constructor.
     */
    private Expr reduceProjCore(Expr c, int idx) {
        Object[] fa = Reducer.getAppFnArgs(c);
        Expr head = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        if (head.tag != Expr.CONST) return null;

        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || !ci.isCtor()) return null;

        int fieldIdx = ci.numParams + idx;
        if (fieldIdx < args.length) {
            return args[fieldIdx];
        }
        return null;
    }

    /**
     * Application equality check (Lean 4's is_def_eq_app).
     * Compares function and arguments of two applications.
     */
    private boolean isDefEqApp(Expr t, Expr s) {
        Object[] tfa = Reducer.getAppFnArgs(t);
        Object[] sfa = Reducer.getAppFnArgs(s);
        Expr tFn = (Expr) tfa[0];
        Expr sFn = (Expr) sfa[0];
        Expr[] tArgs = (Expr[]) tfa[1];
        Expr[] sArgs = (Expr[]) sfa[1];
        if (!isDefEq(tFn, sFn)) return false;
        if (tArgs.length != sArgs.length) return false;
        for (int i = 0; i < tArgs.length; i++) {
            if (!isDefEq(tArgs[i], sArgs[i])) return false;
        }
        return true;
    }

    /**
     * Check whether two app spines have definitionally equal arguments.
     *
     * Lean's `is_def_eq_args` walks the app spine from the outside in, comparing
     * the current `app_arg` before recursing into `app_fn`. This yields a
     * right-to-left argument order for left-associated applications:
     *   (((f a) b) c)  => compare c, then b, then a
     *
     * Keeping the same order matters for trace-space fidelity.
     */
    private boolean isDefEqArgs(Expr t, Expr s) {
        while (t.tag == Expr.APP && s.tag == Expr.APP) {
            if (!isDefEq((Expr) t.o1, (Expr) s.o1)) return false;
            t = (Expr) t.o0;
            s = (Expr) s.o0;
        }
        return t.tag != Expr.APP && s.tag != Expr.APP;
    }

    /** Try eta expansion matching Lean's try_eta_expansion_core. */
    private boolean tryEta(Expr t, Expr s) {
        if (t.tag == Expr.LAM && s.tag != Expr.LAM) {
            Expr sType = whnf(inferTypeOnly(s));
            if (sType.tag != Expr.FORALL) return false;
            Expr newS = Expr.lam(
                sType.o0,
                (Expr) sType.o1,
                Expr.app(Reducer.lift(s, 1, 0), Expr.bvar(0)),
                sType.o3);
            return isDefEq(t, newS);
        }
        return false;
    }

    // ============================================================
    // Eta struct expansion (Lean 4's try_eta_struct)
    // ============================================================

    /**
     * Check if an inductive type is "structure-like":
     * exactly 1 constructor, 0 indices, not recursive.
     */
    private boolean isStructureLike(Name inductName) {
        ConstantInfo ci = env.lookup(inductName);
        return ci != null && ci.isInduct() &&
               ci.ctors != null && ci.ctors.length == 1 &&
               ci.numIndices == 0 && !ci.isRec;
    }

    /**
     * Try eta-struct: if s is a fully-applied constructor of a structure type,
     * check t.proj(i) =?= s.field(i) for each field.
     */
    private boolean tryEtaStructCore(Expr t, Expr s) {
        Object[] sFA = Reducer.getAppFnArgs(s);
        Expr sFn = (Expr) sFA[0];
        Expr[] sArgs = (Expr[]) sFA[1];
        if (sFn.tag != Expr.CONST) return false;

        ConstantInfo ctorCi = env.lookup((Name) sFn.o0);
        if (ctorCi == null || !ctorCi.isCtor()) return false;

        int nparams = ctorCi.numParams;
        int nfields = ctorCi.numFields;
        if (sArgs.length != nparams + nfields) return false;
        Name inductName = ctorCi.inductName;
        if (!isStructureLike(inductName)) return false;

        // Types must match (use inferTypeOnly — called from isDefEq)
        try {
            Expr tType = inferTypeOnly(t);
            Expr sType = inferTypeOnly(s);
            if (!isDefEq(tType, sType)) return false;
        } catch (Exception e) {
            return false;
        }

        // Each field: t.proj(i) =?= s.args[nparams+i]
        for (int i = 0; i < nfields; i++) {
            Expr proj = Expr.proj(inductName, i, t);
            if (!isDefEq(proj, sArgs[nparams + i])) return false;
        }
        return true;
    }

    private boolean tryEtaStruct(Expr t, Expr s) {
        return tryEtaStructCore(t, s) || tryEtaStructCore(s, t);
    }

    /**
     * Any two terms of a zero-field structure type (unit-like) are definitionally equal.
     */
    private boolean isDefEqUnitLike(Expr t, Expr s) {
        try {
            Expr tType = whnf(inferTypeOnly(t));
            Object[] fa = Reducer.getAppFnArgs(tType);
            Expr head = (Expr) fa[0];
            if (head.tag != Expr.CONST) return false;

            Name iName = (Name) head.o0;
            if (!isStructureLike(iName)) return false;

            ConstantInfo indCi = env.lookup(iName);
            if (indCi == null) return false;
            ConstantInfo ctorCi = env.lookup(indCi.ctors[0]);
            if (ctorCi == null || ctorCi.numFields != 0) return false;

            // Both must have the same type (use inferTypeOnly — called from isDefEq)
            return isDefEq(tType, inferTypeOnly(s));
        } catch (Exception e) {
            return false;
        }
    }

    private boolean hasZeroFieldStructureType(Expr e) {
        try {
            Expr type = whnf(inferTypeOnly(e));
            Object[] fa = Reducer.getAppFnArgs(type);
            Expr head = (Expr) fa[0];
            if (head.tag != Expr.CONST) return false;

            Name iName = (Name) head.o0;
            if (!isStructureLike(iName)) return false;

            ConstantInfo indCi = env.lookup(iName);
            if (indCi == null || indCi.ctors.length == 0) return false;
            ConstantInfo ctorCi = env.lookup(indCi.ctors[0]);
            return ctorCi != null && ctorCi.numFields == 0;
        } catch (Exception e1) {
            return false;
        }
    }

    /**
     * Check if both terms are proofs of the same Prop.
     * Returns: 1=equal (both proofs of same Prop), -1=not equal (both Props but different),
     *          0=unknown (not in Prop).
     * Matches Lean 4's is_def_eq_proof_irrel which returns lbool.
     */
    private int proofIrrelevant(Expr t, Expr s) {
        try {
            Expr tt = inferTypeOnly(t);
            if (!isProp(tt)) return 0; // l_undef — not a Prop
            Expr ts = inferTypeOnly(s);
            return isDefEq(tt, ts) ? 1 : -1;
        } catch (Exception e) {
            return 0; // treat inference errors as unknown
        }
    }

    // Make tryUnfoldDef accessible for lazy delta
    private static java.lang.reflect.Method tryUnfoldDefMethod;

    // ============================================================
    // Declaration checking
    // ============================================================

    /**
     * Type-check a ConstantInfo against the environment.
     * Creates a fresh TypeChecker with fuel.
     */
    public static Env checkConstant(Env env, ConstantInfo ci) {
        return checkConstant(env, ci, DEFAULT_FUEL);
    }

    public static Env checkInductiveBundle(Env env, InductiveBundle bundle) {
        return checkInductiveBundle(env, bundle, DEFAULT_FUEL);
    }

    public static Env checkInductiveBundle(Env env, InductiveBundle bundle, long fuel) {
        return InductiveBundleChecker.checkBundle(env, bundle, fuel);
    }

    public static Expr debugExpectedRecursorType(Env env, InductiveBundle bundle, int recIdx, long fuel) {
        InductiveChecker ic = new InductiveChecker(debugEnvWithoutBundle(env, bundle), bundle, fuel);
        ic.prepareRecursorState();
        return ic.debugBuildExpectedRecursorType(recIdx);
    }

    public static Expr debugNormalizedExpectedRecursorType(Env env, InductiveBundle bundle, int recIdx, long fuel) {
        InductiveChecker ic = new InductiveChecker(debugEnvWithoutBundle(env, bundle), bundle, fuel);
        ic.prepareRecursorState();
        return ic.debugBuildNormalizedExpectedRecursorType(recIdx, bundle.recursors[recIdx]);
    }

    public static ConstantInfo.RecursorRule[] debugExpectedRecursorRules(Env env, InductiveBundle bundle, int recIdx, long fuel) {
        return generateExpectedRecursorRules(env, bundle, recIdx, fuel);
    }

    /** Generate Lean-shaped recursor iota rules for a bundle before admission. */
    public static ConstantInfo.RecursorRule[] generateExpectedRecursorRules(Env env, InductiveBundle bundle, int recIdx, long fuel) {
        InductiveChecker ic = new InductiveChecker(debugEnvWithoutBundle(env, bundle), bundle, fuel);
        ic.prepareRecursorState();
        return ic.debugBuildExpectedRecursorRules(recIdx, bundle.recursors[recIdx]);
    }

    private static Env debugEnvWithoutBundle(Env env, InductiveBundle bundle) {
        // At every current call site (generateExpectedRecursorRules,
        // debugExpectedRecursorType, debugNormalizedExpectedRecursorType), the
        // bundle's constants are not yet admitted to env — admission happens
        // afterwards via checkInductiveBundle. So no exclusion is required.
        //
        // The prior implementation rebuilt env via allConstants(), which on
        // PSS / LMDB-backed envs returns locals only (externalLookup is not
        // enumerable). That silently dropped Mathlib, so any inductive whose
        // constructor field types referenced a Mathlib constant (Eq, LE.le,
        // HEq, …) failed recursor generation with "Unknown constant: …".
        //
        // If a future call site admits the bundle before invoking these
        // helpers, replace this with a name-set visibility filter via
        // env.withExternalLookupFiltered — that preserves externals without
        // requiring enumeration.
        return env;
    }

    private static final class ConstantCheckState {
        final TypeChecker tc;
        ConstantCheckState(TypeChecker tc) {
            this.tc = tc;
        }
    }

    private static ConstantCheckState checkConstantPreAdd(Env env, ConstantInfo ci, long fuel,
            Writer traceWriter, boolean phaseTracing) {
        if (ci.isInduct() || ci.isCtor() || ci.isRecursor()) {
            throw new RuntimeException("inductive declarations must be admitted through checkInductiveBundle: " + ci.name);
        }

        // === Check 0: Duplicate universe level parameters ===
        // Following Lean 4 environment.cpp:111-125.
        checkDuplicateUnivParams(ci.levelParams, ci.name);

        // Share common sub-expressions before type-checking.
        java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
        java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
        Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
        Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;
        // Seed intern table with shareCommon results so reduction-created
        // expressions are pointer-identical to proof sub-expressions.
        Expr.seedIntern(scCache);

        TypeChecker tc = new TypeChecker(env, getDefinitionSafety(ci), ci.levelParams);
        tc.setFuel(fuel);
        if (traceWriter != null) tc.setTraceWriter(traceWriter);
        tc.setPhaseTracing(phaseTracing);

        // Theorem: check is_prop first, matching Lean 4's add_theorem.
        if (ci.isThm()) {
            if (phaseTracing) tc.emitPhase("isProp");
            if (!tc.isProp(type)) {
                throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
            }
        }

        // Check type is well-formed (must be a sort).
        if (phaseTracing) tc.emitPhase("checkType");
        tc.ensureSort(tc.check(type));

        // For definitions, theorems, and opaques: check value matches type.
        if (value != null && (ci.isDef() || ci.isThm() || ci.isOpaq())) {
            if (phaseTracing) tc.emitPhase("checkValue");
            Expr inferred = tc.check(value);
            if (phaseTracing) tc.emitPhase("valueDefEqType");
            if (!tc.isDefEq(inferred, type)) {
                String infStr = inferred.toString();
                String declStr = ci.type.toString();
                if (infStr.length() > 300) infStr = infStr.substring(0, 300) + "...";
                if (declStr.length() > 300) declStr = declStr.substring(0, 300) + "...";
                throw new RuntimeException("Type error: Declaration value type does not match declared type for " + ci.name +
                    "\n  inferred: " + infStr + "\n  declared: " + declStr);
            }
        }
        return new ConstantCheckState(tc);
    }

    public static Env checkConstant(Env env, ConstantInfo ci, long fuel) {
        // Quotient primitives: just enable and add (no type-checking needed, they are axioms).
        if (ci.isQuot()) {
            return env.enableQuot().addConstant(ci);
        }

        Expr.enableIntern();
        try {
            checkConstantPreAdd(env, ci, fuel, null, false);
            return env.addConstant(ci);
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    /**
     * Type-check and add-or-REPLACE a constant (SURFACE redefinition: a/defn / a/theorem in a REPL).
     * Identical type-checking to {@link #checkConstant}; only the final add replaces rather than throwing.
     * Kernel proof / install paths keep using the strict {@link #checkConstant}.
     */
    public static Env checkConstantReplace(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            return env.enableQuot().addOrReplaceConstant(ci);
        }
        Expr.enableIntern();
        try {
            checkConstantPreAdd(env, ci, fuel, null, false);
            return env.addOrReplaceConstant(ci);
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    public static Env checkConstantReplace(Env env, ConstantInfo ci) {
        return checkConstantReplace(env, ci, DEFAULT_FUEL);
    }

    static void checkInductiveHeader(Env env, ConstantInfo ci, long fuel) {
        if (!ci.isInduct()) throw new RuntimeException("expected inductive declaration: " + ci.name);
        Expr.enableIntern();
        try {
            checkDuplicateUnivParams(ci.levelParams, ci.name);
            Expr type = Expr.shareCommon(ci.type);
            TypeChecker tc = new TypeChecker(env, getDefinitionSafety(ci), ci.levelParams);
            tc.setFuel(fuel);
            tc.ensureSort(tc.check(type));
            validateInductiveResultSort(ci, tc);
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    static void checkConstructorDeclaration(Env env, ConstantInfo ci, long fuel) {
        if (!ci.isCtor()) throw new RuntimeException("expected constructor declaration: " + ci.name);
        Expr.enableIntern();
        try {
            checkDuplicateUnivParams(ci.levelParams, ci.name);
            Expr type = Expr.shareCommon(ci.type);
            TypeChecker tc = new TypeChecker(env, getDefinitionSafety(ci), ci.levelParams);
            tc.setFuel(fuel);
            tc.ensureSort(tc.check(type));
            ConstantInfo indCi = env.lookup(ci.inductName);
            if (indCi != null && indCi.isInduct()) {
                validateConstructor(env, indCi, ci, tc, !(ci.isUnsafe || indCi.isUnsafe));
            }
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    static void checkRecursorDeclaration(Env env, ConstantInfo ci, long fuel) {
        if (!ci.isRecursor()) throw new RuntimeException("expected recursor declaration: " + ci.name);
        Expr.enableIntern();
        try {
            checkDuplicateUnivParams(ci.levelParams, ci.name);
            Expr type = Expr.shareCommon(ci.type);
            TypeChecker tc = new TypeChecker(env, getDefinitionSafety(ci), ci.levelParams);
            tc.setFuel(fuel);
            tc.ensureSort(tc.check(type));
            if (ci.rules != null) {
                for (ConstantInfo.RecursorRule rule : ci.rules) {
                    ConstantInfo ctorCi = env.lookup(rule.ctor);
                    if (ctorCi != null && ctorCi.isCtor()) {
                        if (rule.nfields != ctorCi.numFields) {
                            throw new RuntimeException("Type error: Recursor rule nfields mismatch for " +
                                ci.name + " constructor " + rule.ctor +
                                ": expected " + ctorCi.numFields + " got " + rule.nfields);
                        }
                    }
                }
            }
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    /** Type-check a declaration with structured NDJSON trace output. */
    public static Env checkConstantTraced(Env env, ConstantInfo ci, long fuel, Writer traceWriter) {
        if (ci.isQuot()) {
            return env.enableQuot().addConstant(ci);
        }
        Expr.enableIntern();
        try {
            checkConstantPreAdd(env, ci, fuel, traceWriter, false);
            try { traceWriter.flush(); } catch (IOException e) {}
            return env.addConstant(ci);
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    /** Like checkConstantTraced, but emits simple phase markers for theorem/definition checking. */
    public static Env checkConstantTracedPhased(Env env, ConstantInfo ci, long fuel, Writer traceWriter) {
        if (ci.isQuot()) {
            return env.enableQuot().addConstant(ci);
        }
        Expr.enableIntern();
        try {
            checkConstantPreAdd(env, ci, fuel, traceWriter, true);
            try { traceWriter.flush(); } catch (IOException e) { throw new RuntimeException(e); }
            return env.addConstant(ci);
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    private static final String[] EMPTY_REDUCER_TRACE = new String[0];

    /**
     * Type-check and return fuel used. For instrumentation.
     */
    public static long checkConstantFuel(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            // Callers must handle env.enableQuot().addConstant(ci)
            return 0;
        }
        Expr.enableIntern();
        try {
            ConstantCheckState state = checkConstantPreAdd(env, ci, fuel, null, false);
            return state.tc.getFuelUsed();
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    /**
     * Type-check and return detailed stats (counters + trace).
     * Returns Object[4]: [fuelUsed (Long), stats (HashMap), trace (String[]), errorOrNull].
     */
    public static Object[] checkConstantFuelStats(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            // Callers must handle env.enableQuot().addConstant(ci)
            return new Object[]{0L, new HashMap<String, Long>(), new String[0], null};
        }
        Expr.enableIntern();
        try {
            TypeChecker tc = null;
            try {
                ConstantCheckState state = checkConstantPreAdd(env, ci, fuel, null, false);
                tc = state.tc;
                env.addConstant(ci);
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), EMPTY_REDUCER_TRACE, null};
            } catch (RuntimeException ex) {
                HashMap<String, Long> stats = tc != null ? tc.getReducerStats() : new HashMap<String, Long>();
                long fuelUsed = tc != null ? tc.getFuelUsed() : 0L;
                return new Object[]{fuelUsed, stats, EMPTY_REDUCER_TRACE, ex.getMessage()};
            } catch (StackOverflowError ex) {
                HashMap<String, Long> stats = tc != null ? tc.getReducerStats() : new HashMap<String, Long>();
                long fuelUsed = tc != null ? tc.getFuelUsed() : 0L;
                long maxDepth = tc != null ? tc.getReducerMaxDepth() : -1L;
                return new Object[]{fuelUsed, stats, EMPTY_REDUCER_TRACE,
                    "StackOverflowError (whnf max depth: " + maxDepth + ")"};
            }
        } finally {
            Expr.disableIntern();
            LeanExprKey.clearThreadCache();
        }
    }

    // ========================================================================
    // Declaration-level validation — following Lean 4 kernel checks
    // ========================================================================

    /**
     * Check for duplicate universe level parameters.
     * Following Lean 4 environment.cpp:111-125.
     */
    private static void checkDuplicateUnivParams(Object[] levelParams, Name declName) {
        if (levelParams == null || levelParams.length <= 1) return;
        java.util.HashSet<Object> seen = new java.util.HashSet<>();
        for (Object lp : levelParams) {
            if (!seen.add(lp)) {
                throw new RuntimeException("Duplicate universe level parameter '" + lp + "' in " + declName);
            }
        }
    }

    private static byte getDefinitionSafety(ConstantInfo ci) {
        if (ci.isDef()) {
            return ci.safety;
        }
        if (ci.isUnsafe) {
            return DEFN_UNSAFE;
        }
        return DEFN_SAFE;
    }

    /**
     * Validate that the inductive type's result (after stripping params+indices) is a sort,
     * and that numParams doesn't exceed the actual forall binder count.
     * Following Lean 4 inductive.cpp:210-261.
     */
    private static void validateInductiveResultSort(ConstantInfo indCi, TypeChecker tc) {
        Expr indType = tc.whnf(indCi.type);
        int piCount = 0;
        while (indType.tag == Expr.FORALL) {
            long fid = tc.nextFvarId();
            Expr fvar = Expr.fvar(fid);
            tc.addLocalDecl(fid, indType.o0, (Expr) indType.o1);
            indType = tc.whnf(Reducer.instantiate1((Expr) indType.o2, fvar));
            piCount++;
        }
        if (piCount < indCi.numParams) {
            throw new RuntimeException("Inductive " + indCi.name +
                " type has " + piCount + " forall binders but numParams=" + indCi.numParams);
        }
        if (indType.tag != Expr.SORT) {
            throw new RuntimeException("Inductive " + indCi.name + " result type is not a sort: " + indType);
        }
    }

    /**
     * Validate a single constructor against its inductive type.
     * Following Lean 4 inductive.cpp check_constructors (lines 412-453)
     * and check_positivity (lines 391-408).
     *
     * Checks:
     * 1. Constructor parameters match inductive's parameters (by def-eq)
     * 2. Constructor return type is a valid application of the inductive
     * 3. No inductive occurrences in indices (Lean 4 issue #2125)
     * 4. Field universe levels ≤ inductive's result level (or inductive is Prop)
     * 5. Strict positivity: no negative recursive occurrences
     */
    private static void validateConstructor(Env env, ConstantInfo indCi, ConstantInfo ctorCi,
            TypeChecker tc, boolean checkStrictPositivity) {
        int np = indCi.numParams;
        int ni = indCi.numIndices;

        // Collect names of all inductives in the mutual group
        java.util.HashSet<Name> inductiveNames = new java.util.HashSet<>();
        if (indCi.all != null) {
            for (Object n : indCi.all) inductiveNames.add((Name) n);
        } else {
            inductiveNames.add(indCi.name);
        }

        // Determine the result universe level by stripping params+indices from the ind type
        Expr indType = tc.whnf(indCi.type);
        Expr[] paramFvars = new Expr[np];
        for (int i = 0; i < np; i++) {
            if (indType.tag != Expr.FORALL) {
                throw new RuntimeException("Inductive " + indCi.name + " type has fewer binders than numParams=" + np);
            }
            long fid = tc.nextFvarId();
            Expr fvar = Expr.fvar(fid);
            tc.addLocalDecl(fid, indType.o0, (Expr) indType.o1);
            paramFvars[i] = fvar;
            indType = tc.whnf(Reducer.instantiate1((Expr) indType.o2, fvar));
        }
        for (int i = 0; i < ni; i++) {
            if (indType.tag != Expr.FORALL) break;
            long fid = tc.nextFvarId();
            indType = tc.whnf(Reducer.instantiate1((Expr) indType.o2, Expr.fvar(fid)));
        }
        if (indType.tag != Expr.SORT) {
            throw new RuntimeException("Inductive " + indCi.name + " result type is not a sort: " + indType);
        }
        Level resultLevel = (Level) indType.o0;
        boolean resultIsZero = Level.isZero(resultLevel);

        // Walk constructor type.
        // Lean 4 does NOT whnf the constructor type itself — it must be manifest foralls.
        // Only field types (binding_domain) are whnf'd for positivity/universe checks.
        Expr ctorType = ctorCi.type;

        // Check 1: Constructor params must match inductive's params
        for (int i = 0; i < np; i++) {
            if (ctorType.tag != Expr.FORALL) {
                throw new RuntimeException("Constructor " + ctorCi.name + " has fewer binders than numParams=" + np);
            }
            // Parameter domain must be def-eq to inductive's param type
            Expr paramType = (Expr) ctorType.o1;
            Expr expectedParamType = tc.inferType(paramFvars[i]);
            if (!tc.isDefEq(paramType, expectedParamType)) {
                throw new RuntimeException("Constructor " + ctorCi.name +
                    " param #" + (i + 1) + " type does not match inductive parameter");
            }
            ctorType = Reducer.instantiate1((Expr) ctorType.o2, paramFvars[i]);
        }

        // Check fields — must also be manifest foralls (no whnf on outer structure)
        int fieldIdx = 0;
        while (ctorType.tag == Expr.FORALL) {
            Expr fieldType = (Expr) ctorType.o1;

            // Check 4: Field universe ≤ result universe (or result is Prop)
            // Following Lean 4 inductive.cpp:437-438:
            //   if (!(is_geq(m_result_level, sort_level(s)) || is_zero(m_result_level)))
            if (!resultIsZero) {
                try {
                    Expr fieldSort = tc.ensureSort(tc.inferType(fieldType));
                    Level fieldLevel = (Level) fieldSort.o0;
                    if (!Level.leq(fieldLevel, resultLevel)) {
                        throw new RuntimeException("Universe level of field #" + (fieldIdx + 1) +
                            " of constructor " + ctorCi.name + " is too large for " + indCi.name);
                    }
                } catch (RuntimeException e) {
                    if (e.getMessage() != null && e.getMessage().startsWith("Universe level"))
                        throw e;
                }
            }

            // Check 5: Strict positivity. Lean skips only this check for unsafe
            // inductives; all shape, universe, and result checks still apply.
            if (checkStrictPositivity) {
                checkPositivity(tc, fieldType, inductiveNames, paramFvars, ctorCi.name, fieldIdx + 1);
            }

            long fid = tc.nextFvarId();
            Expr fvar = Expr.fvar(fid);
            tc.addLocalDecl(fid, ctorType.o0, fieldType);
            ctorType = Reducer.instantiate1((Expr) ctorType.o2, fvar);
            fieldIdx++;
        }

        // After fields, the remaining expression is the return type.
        // Lean 4 does NOT whnf the return type — it must structurally be
        // a valid application of the inductive type (manifest, not hidden
        // behind definitions). This matches check_constructors line 449.
        Expr retType = ctorType;
        Expr retHead = retType;
        java.util.ArrayList<Expr> retArgs = new java.util.ArrayList<>();
        while (retHead.tag == Expr.APP) {
            retArgs.add(0, (Expr) retHead.o1);
            retHead = (Expr) retHead.o0;
        }
        if (retHead.tag != Expr.CONST || !inductiveNames.contains((Name) retHead.o0)) {
            throw new RuntimeException("Constructor " + ctorCi.name +
                " return type is not an application of " + indCi.name);
        }
        if (retArgs.size() != np + ni) {
            throw new RuntimeException("Constructor " + ctorCi.name +
                " return type has wrong number of arguments: expected " + (np + ni) + " got " + retArgs.size());
        }
        // Check level params match: the const in return type must use same levels as the inductive
        // (detects swapped level params like {u2, u1} vs {u1, u2})
        Object[] retLevels = Reducer.constLevels(retHead);
        if (retLevels.length != indCi.levelParams.length) {
            throw new RuntimeException("Constructor " + ctorCi.name +
                " return type has wrong number of level params");
        }
        for (int i = 0; i < retLevels.length; i++) {
            Level expected = Level.param((Name) indCi.levelParams[i]);
            if (!retLevels[i].equals(expected)) {
                throw new RuntimeException("Constructor " + ctorCi.name +
                    " return type level param #" + (i + 1) + " does not match inductive");
            }
        }
        // Params in return type must match (def-eq to param fvars)
        for (int i = 0; i < np; i++) {
            if (!tc.isDefEq(retArgs.get(i), paramFvars[i])) {
                throw new RuntimeException("Constructor " + ctorCi.name +
                    " return type parameter #" + (i + 1) + " does not match");
            }
        }
        // Check 3: No inductive occurrences in indices
        for (int i = np; i < retArgs.size(); i++) {
            if (exprContainsNameOrFvar(retArgs.get(i), inductiveNames)) {
                throw new RuntimeException("Constructor " + ctorCi.name +
                    " has inductive type in index position (unsound, see Lean 4 #2125)");
            }
        }
    }

    /**
     * Strict positivity check for a constructor field type.
     * Following Lean 4 inductive.cpp:391-408.
     *
     * A field type is positive if:
     * - It contains no references to the inductives being defined, OR
     * - It is a valid direct application of one of the inductives, OR
     * - It is a pi type where the domain has NO inductive references
     *   and the codomain is positive (recursively)
     *
     * Any other pattern (inductive in domain of arrow, or inductive
     * applied with wrong args) is a negative/non-positive occurrence.
     */
    private static void checkPositivity(TypeChecker tc, Expr type,
            java.util.HashSet<Name> inductiveNames, Expr[] paramFvars, Name ctorName, int argIdx) {
        type = tc.whnf(type);

        // Case 1: No inductive occurrences at all — OK
        if (!exprContainsName(type, inductiveNames)) return;

        if (type.tag == Expr.FORALL) {
            // Case 2: Pi type — domain must NOT contain inductive (negative position!)
            Expr domain = (Expr) type.o1;
            if (exprContainsName(domain, inductiveNames)) {
                throw new RuntimeException("Constructor " + ctorName +
                    " arg #" + argIdx + " has non-positive occurrence of inductive type");
            }
            // Codomain: check recursively (positive position)
            long fid = tc.nextFvarId();
            Expr fvar = Expr.fvar(fid);
            tc.addLocalDecl(fid, type.o0, domain);
            Expr body = Reducer.instantiate1((Expr) type.o2, fvar);
            checkPositivity(tc, body, inductiveNames, paramFvars, ctorName, argIdx);
        } else {
            // Case 3: Must be a valid inductive application or a well-formed nested inductive.
            if (isValidInductiveOccurrence(tc, type, inductiveNames, paramFvars)) {
                return;
            }
            if (isValidNestedInductiveOccurrence(tc, type, inductiveNames, paramFvars)) {
                return;
            }
            // Case 4: Contains inductive but not as valid application
            throw new RuntimeException("Constructor " + ctorName +
                " arg #" + argIdx + " has non-valid occurrence of inductive type");
        }
    }

    private static boolean isValidInductiveOccurrence(TypeChecker tc, Expr type,
            java.util.HashSet<Name> inductiveNames, Expr[] paramFvars) {
        Object[] app = decomposeApp(type);
        Expr head = (Expr) app[0];
        Expr[] args = (Expr[]) app[1];
        if (head.tag != Expr.CONST) return false;

        Name headName = (Name) head.o0;
        if (!inductiveNames.contains(headName)) return false;

        ConstantInfo headCi = tc.getEnv().lookup(headName);
        if (headCi == null || !headCi.isInduct()) return false;
        if (args.length != headCi.numParams + headCi.numIndices) return false;
        if (paramFvars.length < headCi.numParams) return false;

        for (int i = 0; i < headCi.numParams; i++) {
            if (!tc.isDefEq(args[i], paramFvars[i])) {
                return false;
            }
        }
        for (int i = headCi.numParams; i < args.length; i++) {
            if (exprContainsName(args[i], inductiveNames)) {
                return false;
            }
        }
        return true;
    }

    private static boolean isValidNestedInductiveOccurrence(TypeChecker tc, Expr type,
            java.util.HashSet<Name> inductiveNames, Expr[] paramFvars) {
        Object[] app = decomposeApp(type);
        Expr head = (Expr) app[0];
        Expr[] args = (Expr[]) app[1];
        if (head.tag != Expr.CONST) return false;

        Name headName = (Name) head.o0;
        if (inductiveNames.contains(headName)) return false;

        ConstantInfo headCi = tc.getEnv().lookup(headName);
        if (headCi == null || !headCi.isInduct()) return false;
        if (args.length < headCi.numParams) return false;

        java.util.HashSet<Long> allowedParamIds = new java.util.HashSet<>(paramFvars.length * 2 + 1);
        for (Expr paramFvar : paramFvars) {
            if (paramFvar != null && paramFvar.tag == Expr.FVAR) {
                allowedParamIds.add(paramFvar.longVal);
            }
        }

        boolean isNested = false;
        boolean hasUnexpectedFVar = false;
        for (int i = 0; i < headCi.numParams; i++) {
            Expr paramArg = args[i];
            if (exprContainsUnexpectedFVar(paramArg, allowedParamIds)) {
                hasUnexpectedFVar = true;
            }
            if (exprContainsName(paramArg, inductiveNames)) {
                isNested = true;
            }
        }
        if (isNested && hasUnexpectedFVar) {
            throw new RuntimeException("invalid nested inductive datatype '" + headName +
                "', nested inductive datatype parameters cannot contain local variables");
        }
        return isNested;
    }

    private static Object[] decomposeApp(Expr e) {
        int argCount = 0;
        Expr head = e;
        while (head.tag == Expr.APP) {
            argCount++;
            head = (Expr) head.o0;
        }
        Expr[] args = new Expr[argCount];
        Expr cur = e;
        for (int i = argCount - 1; i >= 0; i--) {
            args[i] = (Expr) cur.o1;
            cur = (Expr) cur.o0;
        }
        return new Object[]{head, args};
    }

    private static boolean exprContainsUnexpectedFVar(Expr e, java.util.HashSet<Long> allowedFVars) {
        if (e == null) return false;
        switch (e.tag) {
            case Expr.FVAR:
                return !allowedFVars.contains(e.longVal);
            case Expr.APP:
                return exprContainsUnexpectedFVar((Expr) e.o0, allowedFVars)
                    || exprContainsUnexpectedFVar((Expr) e.o1, allowedFVars);
            case Expr.LAM:
            case Expr.FORALL:
                return exprContainsUnexpectedFVar((Expr) e.o1, allowedFVars)
                    || exprContainsUnexpectedFVar((Expr) e.o2, allowedFVars);
            case Expr.LET:
                return exprContainsUnexpectedFVar((Expr) e.o1, allowedFVars)
                    || exprContainsUnexpectedFVar((Expr) e.o2, allowedFVars)
                    || (e.o3 instanceof Expr && exprContainsUnexpectedFVar((Expr) e.o3, allowedFVars));
            case Expr.PROJ:
                return exprContainsUnexpectedFVar((Expr) e.o1, allowedFVars);
            case Expr.MDATA:
                return exprContainsUnexpectedFVar((Expr) e.o1, allowedFVars);
            default:
                return false;
        }
    }

    /** Expose Reducer.constLevels for the package. */
    static Object[] constLevels(Expr e) {
        return Reducer.constLevels(e);
    }

    /**
     * Like exprContainsName but also checks for const references (not fvars).
     * For index checking after instantiation with fvars, the inductive
     * reference might appear as a const in a nested position.
     */
    private static boolean exprContainsNameOrFvar(Expr e, java.util.HashSet<Name> names) {
        return exprContainsName(e, names);
    }

    /**
     * Check if an expression contains a reference to any name in the given set.
     * Used for detecting nested inductives: a field type like Array(Syntax)
     * contains "Syntax" in Array's parameters.
     */
    private static boolean exprContainsName(Expr e, java.util.HashSet<Name> names) {
        if (e == null) return false;
        switch (e.tag) {
            case Expr.CONST:
                return names.contains((Name) e.o0);
            case Expr.APP:
                return exprContainsName((Expr) e.o0, names) || exprContainsName((Expr) e.o1, names);
            case Expr.LAM:
            case Expr.FORALL:
                return exprContainsName((Expr) e.o1, names) || exprContainsName((Expr) e.o2, names);
            case Expr.LET:
                return exprContainsName((Expr) e.o1, names) || exprContainsName((Expr) e.o2, names)
                    || (e.o3 instanceof Expr && exprContainsName((Expr) e.o3, names));
            case Expr.PROJ:
                return exprContainsName((Expr) e.o1, names);
            case Expr.MDATA:
                return exprContainsName((Expr) e.o1, names);
            default:
                return false;
        }
    }

    /**
     * Reindex bvars from constructor type context to RHS/IH body context.
     * Three-way split for function-type recursive fields:
     *   bvar(k < j):            inner forall vars → unchanged (maps to IH lambda binders)
     *   bvar(j ≤ k < fi + j):   field refs → bvar(k + nf - fi)
     *   bvar(k ≥ fi + j):       param refs → bvar(k + nmNmi + nf - fi)
     *
     * For simple fields (no extra pis), j=0 and this reduces to the two-way split.
     *
     * @param e expression at ctor depth np+fi+j
     * @param j number of inner forall vars to preserve (extra pi depth)
     * @param fi field index (0-based)
     * @param nmNmi number of motives + minors (inserted binders)
     * @param nf total number of fields
     */
    static Expr reindexBvarsIH(Expr e, int j, int fi, int nmNmi, int nf) {
        if (e.bvarRange() == 0) return e;

        switch (e.tag) {
            case Expr.BVAR: {
                long k = e.longVal;
                if (k < j) {
                    return e; // inner forall var → maps to IH lambda binder
                } else if (k < fi + j) {
                    return Expr.bvar(k + nf - fi); // field ref
                } else {
                    return Expr.bvar(k + nmNmi + nf - fi); // param ref
                }
            }
            case Expr.APP: {
                Expr fn = reindexBvarsIH((Expr) e.o0, j, fi, nmNmi, nf);
                Expr arg = reindexBvarsIH((Expr) e.o1, j, fi, nmNmi, nf);
                if (fn == e.o0 && arg == e.o1) return e;
                return Expr.app(fn, arg);
            }
            case Expr.LAM: {
                Expr ty = reindexBvarsIH((Expr) e.o1, j, fi, nmNmi, nf);
                Expr body = reindexBvarsIH((Expr) e.o2, j + 1, fi, nmNmi, nf);
                if (ty == e.o1 && body == e.o2) return e;
                return Expr.lam(e.o0, ty, body, e.o3);
            }
            case Expr.FORALL: {
                Expr ty = reindexBvarsIH((Expr) e.o1, j, fi, nmNmi, nf);
                Expr body = reindexBvarsIH((Expr) e.o2, j + 1, fi, nmNmi, nf);
                if (ty == e.o1 && body == e.o2) return e;
                return Expr.forall(e.o0, ty, body, e.o3);
            }
            default:
                return e;
        }
    }

    /**
     * Deep structural equality for Expr that handles level array comparison.
     * Standard Expr.equals uses Object.equals for the levels container,
     * which fails for different array instances with the same contents.
     */
    static boolean exprDeepEquals(Expr a, Expr b) {
        if (a == b) return true;
        if (a == null || b == null) return false;
        if (a.tag != b.tag) return false;

        switch (a.tag) {
            case Expr.BVAR:
                return a.longVal == b.longVal;
            case Expr.SORT:
                return a.o0.equals(b.o0);
            case Expr.CONST: {
                if (!a.o0.equals(b.o0)) return false;
                Object[] la = Reducer.constLevels(a);
                Object[] lb = Reducer.constLevels(b);
                if (la.length != lb.length) return false;
                for (int i = 0; i < la.length; i++) {
                    if (!la[i].equals(lb[i])) return false;
                }
                return true;
            }
            case Expr.APP:
                return exprDeepEquals((Expr) a.o0, (Expr) b.o0)
                    && exprDeepEquals((Expr) a.o1, (Expr) b.o1);
            case Expr.LAM:
            case Expr.FORALL:
                // Skip binder name (o0) — decorative in CIC (alpha-equivalence).
                // Lean 4's mk_rec_rules uses fresh hygienic names that differ from
                // raw constructor names. Binder info (o3) IS semantically relevant.
                return exprDeepEquals((Expr) a.o1, (Expr) b.o1)
                    && exprDeepEquals((Expr) a.o2, (Expr) b.o2)
                    && java.util.Objects.equals(a.o3, b.o3);
            case Expr.LET:
                return java.util.Objects.equals(a.o0, b.o0)
                    && exprDeepEquals((Expr) a.o1, (Expr) b.o1)
                    && exprDeepEquals((Expr) a.o2, (Expr) b.o2)
                    && exprDeepEquals((Expr) a.o3, (Expr) b.o3);
            case Expr.PROJ:
                return a.o0.equals(b.o0) && a.longVal == b.longVal
                    && exprDeepEquals((Expr) a.o1, (Expr) b.o1);
            case Expr.LIT_NAT:
            case Expr.LIT_STR:
                return a.o0.equals(b.o0);
            case Expr.FVAR:
            case Expr.MVAR:
                return a.longVal == b.longVal;
            default:
                return a.equals(b);
        }
    }
}
