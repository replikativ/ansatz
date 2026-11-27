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
    // lean4#14806: successful is_def_eq results are a hash-ordered PAIR cache (identity +
    // structural), mirroring the failure cache below. NOT a union-find: is_def_eq is a sound
    // but incomplete semi-decision procedure and therefore not transitive, so an equivalence
    // closure of successes made the answer depend on query order (that was EquivManager).
    // type_checker::state (type_checker.h:28-44): one structural map per role, hashed by the
    // node's stored hash, identity the first thing a probe tests.
    private final ExprMap<Expr> inferCache;       // m_infer_type[0]
    private final ExprMap<Expr> inferOnlyCache;   // m_infer_type[1]
    private final ExprPairSet success;            // m_success  (lean4#14806 pair cache)
    private final ExprPairSet failure;            // m_failure
    // Free variable ids. Lean's caches assume "free variables are globally unique with fixed
    // types" (type_checker.h); Lean keeps the kernel's own locals and the inductive module's
    // apart with separate name generators (g_kernel_fresh vs inductive.cpp's g_ind_fresh).
    // Here a local is a numeric id, and callers (InductiveChecker, the recursor and nested
    // generators, the elaborator) number theirs from small counters. The checker's own locals
    // (binders opened while inferring, reducing or comparing) take ids from a disjoint range
    // starting at KERNEL_FRESH_BASE, so a caller can never hand out an id the checker already
    // used — and cached under — for a different local.
    public static final long KERNEL_FRESH_BASE = 1L << 62;
    private long nextId;
    private int isDefEqDepth;
    private final byte definitionSafety;
    private final HashSet<Object> allowedLevelParams;
    public boolean tracing;

    // isDefEq diagnostic counters
    long isDefEqCalls;
    long isDefEqQuickHits;    // pointer equality or hash mismatch
    long isDefEqEquivHits;    // success-cache hits (was EquivManager hits)
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
                "\",\"success_cached\":" + succeededBefore(lhs, rhs) + "}\n");
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
                ",\"same_local_expr_id\":" + (domT.storeId >= 0 && domT.storeId == domS.storeId) +
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

    /** Node count of `e` as a tree, capped. */
    static int exprSize(Expr e, int cap) {
        java.util.ArrayDeque<Expr> st = new java.util.ArrayDeque<>(); st.push(e); int n = 0;
        while (!st.isEmpty() && n < cap) {
            Expr x = st.pop(); n++;
            switch (x.tag) {
                case Expr.APP: st.push((Expr) x.o0); st.push((Expr) x.o1); break;
                case Expr.LAM: case Expr.FORALL: st.push((Expr) x.o1); st.push((Expr) x.o2); break;
                case Expr.LET: st.push((Expr) x.o1); st.push((Expr) x.o2); st.push((Expr) x.o3); break;
                case Expr.MDATA: case Expr.PROJ: st.push((Expr) x.o1); break;
                default: break;
            }
        }
        return n;
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

    /** Set the delta-reduction allow predicate for reducible mode (transparency=0): the names
     *  it accepts are unfolded too (Reducer.canUnfold). */
    public void setDeltaAllowPredicate(java.util.function.Predicate<Name> pred) { reducer.setDeltaAllowPredicate(pred); }

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
        this.definitionSafety = ConstantInfo.validateDefinitionSafety(definitionSafety);
        this.allowedLevelParams = mkAllowedLevelParamSet(allowedLevelParams);
        this.reducer = new Reducer(env);
        this.inferCache = new ExprMap<>(8);
        this.inferOnlyCache = new ExprMap<>(8);
        this.success = new ExprPairSet(8);
        this.failure = new ExprPairSet(8);
        this.nextId = KERNEL_FRESH_BASE;
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

    /** Spend what remains of prev's fuel budget, as one declaration checked in two phases. */
    void continueFuel(TypeChecker prev) {
        this.reducer.continueFuel(prev.reducer);
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
     * Lean 4 master (type_checker.cpp, lean4#14807):
     *   is_prop(e) = is_zero(sort_level(ensure_sort_core(infer_type(e), e)))
     * The type of e must whnf to a SORT; anything else is a "type expected" ERROR, not
     * "not a Prop". The pre-fix syntactic test (tag==SORT && level==ZERO) answered false on a
     * STUCK sort, which let data be projected out of / eliminated from a proposition whose
     * sort only reduces under one of two definitionally-equal spellings (arena
     * proj-of-subst-prop, rec-of-subst-prop). Level.isZero normalizes (max/imax), matching
     * Lean's is_zero rather than a syntactic ZERO tag.
     */
    private boolean isProp(Expr e) {
        Expr t = whnf(inferTypeOnly(e));
        if (t.tag != Expr.SORT) {
            throw new RuntimeException("Type error: type expected, got " + t + " (is_prop on a stuck sort — lean4#14807)");
        }
        return Level.isZero((Level) t.o0);
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

    /** Public entry for callers that check open terms under known free variables
     *  (the nested-inductive parameter context, lean4#14577). */
    public void addLocal(long id, Object name, Expr type) {
        lctxAddLocal(id, name, type);
    }

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
    /** The locals a binder telescope introduces, in order (Lean's `buffer<expr> fvars`). */
    private static final class Telescope {
        Expr[] fvars = new Expr[8];
        long[] ids = new long[8];
        int n = 0;

        void push(long id) {
            if (n == ids.length) {
                fvars = java.util.Arrays.copyOf(fvars, 2 * n);
                ids = java.util.Arrays.copyOf(ids, 2 * n);
            }
            fvars[n] = Expr.fvar(id);
            ids[n] = id;
            n++;
        }

        /** Restore the context the telescope started from (Lean's `flet<local_ctx>`). */
        void removeFrom(TypeChecker tc) {
            for (int i = n - 1; i >= 0; i--) tc.lctxRemove(ids[i]);
        }
    }

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
        checkSystem();
        ExprMap<Expr> cache = inferOnly ? inferOnlyCache : inferCache;
        Expr cached = cache.get(e);
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
                    if (ci.isUnsafeDeclaration() && definitionSafety != DEFN_UNSAFE) {
                        throw new RuntimeException("Type error: invalid declaration, it uses unsafe declaration '" + e.o0 + "'");
                    }
                    if (ci.isDef() && ci.getDefinitionSafety() == DEFN_PARTIAL && definitionSafety == DEFN_SAFE) {
                        throw new RuntimeException("Type error: invalid declaration, safe declaration must not contain partial declaration '" + e.o0 + "'");
                    }
                    for (Object level : levels) {
                        checkLevel((Level) level);
                    }
                }
                if (ci.levelParams.length == 0) {
                    result = ci.type;
                } else {
                    HashMap<Object, Level> subst = new HashMap<>(ci.levelParams.length * 2);
                    for (int i = 0; i < ci.levelParams.length; i++) {
                        subst.put(ci.levelParams[i], (Level) levels[i]);
                    }
                    result = Reducer.instantiateLevelParams(ci.type, subst);
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
                // Lean 4 v4.36 infer_lambda: check each domain, then extend the context.
                Telescope t = new Telescope();
                try {
                    Expr cur = e;
                    while (cur.tag == Expr.LAM) {
                        Expr d = Reducer.instantiateRev((Expr) cur.o1, t.n, t.fvars, 0);
                        if (!inferOnly) ensureSort(inferTypeCore(d, false));
                        long id = freshId();
                        lctxAddLocalWithInfo(id, cur.o0, d, cur.o3);
                        t.push(id);
                        cur = (Expr) cur.o2;
                    }
                    Expr r = inferTypeCore(Reducer.instantiateRev(cur, t.n, t.fvars, 0), inferOnly);
                    result = mkPi(t.ids, t.n, Reducer.cheapBetaReduce(r), false);
                } finally {
                    t.removeFrom(this);
                }
                break;
            }

            case Expr.FORALL: {
                // Lean 4 v4.36 infer_pi: check each domain, then extend the context.
                Telescope t = new Telescope();
                java.util.ArrayList<Level> us = new java.util.ArrayList<>();
                try {
                    Expr cur = e;
                    while (cur.tag == Expr.FORALL) {
                        Expr d = Reducer.instantiateRev((Expr) cur.o1, t.n, t.fvars, 0);
                        us.add((Level) ensureSort(inferTypeCore(d, inferOnly)).o0);
                        long id = freshId();
                        lctxAddLocal(id, cur.o0, d);
                        t.push(id);
                        cur = (Expr) cur.o2;
                    }
                    Expr s = ensureSort(inferTypeCore(Reducer.instantiateRev(cur, t.n, t.fvars, 0), inferOnly));
                    Level r = (Level) s.o0;
                    for (int i = us.size() - 1; i >= 0; i--) r = Level.imax(us.get(i), r);
                    result = Expr.sort(r, Level.hasParam(r));
                } finally {
                    t.removeFrom(this);
                }
                break;
            }

            case Expr.LET: {
                // Lean 4 v4.36 infer_let: check the type and the value, then extend the context.
                Telescope t = new Telescope();
                try {
                    Expr cur = e;
                    while (cur.tag == Expr.LET) {
                        Expr type = Reducer.instantiateRev((Expr) cur.o1, t.n, t.fvars, 0);
                        Expr val = Reducer.instantiateRev((Expr) cur.o2, t.n, t.fvars, 0);
                        if (!inferOnly) {
                            ensureSort(inferTypeCore(type, false));
                            if (!isDefEq(inferTypeCore(val, false), type)) {
                                throw new RuntimeException("Type error: Let value type mismatch");
                            }
                        }
                        long id = freshId();
                        lctxAddLet(id, cur.o0, type, val);
                        t.push(id);
                        cur = (Expr) cur.o3;
                    }
                    Expr r = inferTypeCore(Reducer.instantiateRev(cur, t.n, t.fvars, 0), inferOnly);
                    result = mkPi(t.ids, t.n, Reducer.cheapBetaReduce(r), true);
                } finally {
                    t.removeFrom(this);
                }
                break;
            }

            case Expr.LIT_NAT:
                // lean4#14849: a literal larger than LEAN_NAT_MAX_SIZE is refused at inference
                Reducer.checkNatSize((java.math.BigInteger) e.o0);
                result = Expr.mkConst(Name.NAT, clojure.lang.PersistentVector.EMPTY, false);
                break;

            case Expr.LIT_STR:
                result = Expr.mkConst(Name.STRING, clojure.lang.PersistentVector.EMPTY, false);
                break;

            case Expr.MDATA:
                result = inferTypeCore((Expr) e.o1, inferOnly);
                break;

            case Expr.PROJ: {
                // The field index is a Nat. Expr.proj refuses a negative one; the range check keeps
                // the int conversions below exact (a wrapped index would type one field and reduce
                // to another).
                if (e.longVal < 0 || e.longVal > Integer.MAX_VALUE)
                    throw new RuntimeException("Type error: invalid projection index " + e.longVal);
                Expr structType = whnf(inferTypeCore((Expr) e.o1, inferOnly));
                Object[] fa = Reducer.getAppFnArgs(structType);
                Expr head = (Expr) fa[0];
                Expr[] typeArgs = (Expr[]) fa[1];
                if (head.tag != Expr.CONST) {
                    throw new RuntimeException("Type error: Projection target not an inductive");
                }
                // Lean infer_proj (type_checker.cpp:278-280): the projection's structure name must be
                // the head of the projected term's type (leanprover/lean4#14631 / #14632).
                if (!head.o0.equals(e.o0)) {
                    throw new RuntimeException("Type error: invalid projection: " + e.o0 + " is not the structure of the projected term (" + head.o0 + ")");
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
        cache.put(e, result);
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
        // A successful result is cached as a PAIR (lean4#14806 cache_success), never as an
        // equivalence class: is_def_eq is not transitive, so closing successes under
        // transitivity made later answers depend on which pairs were asked first.
        boolean result = isDefEqCore(t, s);
        if (result) {
            emitEquivTrace("cache_success.before", t, s);
            cacheSuccess(t, s);
            emitEquivTrace("cache_success.after", t, s);
        }
        return result;
    }

    // Lean's check_system(do_check_interrupted) at the head of is_def_eq_core and
    // infer_type_core (type_checker.cpp:322, :1118): a check whose time goes into is_def_eq
    // cache probes and structural comparisons never reaches the reducer's fuel counter, so
    // the interruption a timeout delivers must be observed here too.
    private long systemCheckCount;
    private void checkSystem() {
        if ((++systemCheckCount & 0xFFF) == 0 && Thread.interrupted()) {
            throw new KernelAbort("Type checking interrupted (timeout)");
        }
    }

    private boolean isDefEqCore(Expr t, Expr s) {
        checkSystem();
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
        // Lean (post-#14806): `if (t == s || succeeded_before(t, s)) return l_true;` —
        // pointer or structural equality, or a previously SUCCESSFUL pair. No union-find,
        // no merging, no transitive closure. `useHash` is retained for call-site
        // compatibility; structural equality checks the hash first regardless.
        if (t == s || succeededBefore(t, s) || structurallyEqual(t, s)) {
            isDefEqEquivHits++;
            return 1;
        }
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
                // isEqp tests actual Java object identity, never local store IDs.
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
        Expr tn = reducer.whnfCore(t, false, true);
        Expr sn = reducer.whnfCore(s, false, true);
        boolean whnfChanged = !tn.isEqp(t) || !sn.isEqp(s);

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
            && succeededBefore(tn, sn)
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
            if (lazyDeltaProjReduction((Expr) tn.o1, (Expr) sn.o1, tn.longVal)) {
                if (doEmit) emitTrace(lFp, rFp, true, "proj_delta");
                return true;
            }
        }

        // Step 6: Second whnf_core pass with full flags
        {
            Expr tn2Raw = reducer.whnfCore(tn, false, false);
            Expr sn2Raw = reducer.whnfCore(sn, false, false);
            boolean whnf2Changed = !tn2Raw.isEqp(tn) || !sn2Raw.isEqp(sn);
            Expr tn2 = tn2Raw;
            Expr sn2 = sn2Raw;
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

    // Output of lazyDeltaReduction on an "unknown" (0) result: the pair it reduced to, which
    // the caller reads immediately. Nested isDefEq calls (from the Nat/Int probes, the quick
    // check's binder comparison, argument comparison, K) run lazyDeltaReduction themselves and
    // overwrite this array, so the loop keeps its pair in locals and writes it here only on
    // return — like Lean's lazy_delta_reduction, which updates the caller's own references.
    private final Expr[] deltaHolder = new Expr[2];

    private int lazyDeltaUnknown(Expr tn, Expr sn) {
        deltaHolder[0] = tn;
        deltaHolder[1] = sn;
        return 0;
    }

    /**
     * Lazy delta reduction. Returns: 1=equal, -1=not equal, 0=unknown; on 0, deltaHolder
     * holds the reduced pair.
     */
    private int lazyDeltaReduction(Expr tn, Expr sn) {
        for (int iter = 0; iter < 10000; iter++) {
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
                return lazyDeltaUnknown(tn, sn); // Neither side can be unfolded
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
                    if (unfolded == null) return lazyDeltaUnknown(tn, sn);
                    tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
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
                    if (unfolded == null) return lazyDeltaUnknown(tn, sn);
                    sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
                    emitDeltaTrace("unfold.right", tn, sn);
                }
            } else {
                // Both sides are definitions — use hints to decide
                long tHints = dtInfo.getHintsCode();
                long sHints = dsInfo.getHintsCode();
                int cmp = compareHints(tHints, sHints);

                if (cmp < 0) {
                    // Unfold left (higher height / more complex)
                    Expr unfolded = reducer.tryUnfoldDef(tnHead);
                    if (unfolded == null) return lazyDeltaUnknown(tn, sn);
                    tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
                    emitDeltaTrace("unfold.left", tn, sn);
                } else if (cmp > 0) {
                    // Unfold right
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return lazyDeltaUnknown(tn, sn);
                    sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
                    emitDeltaTrace("unfold.right", tn, sn);
                } else {
                    // Same hint level — Lean takes this shortcut when is_delta
                    // resolves both sides to the same declaration object, even if
                    // the head constants carry syntactically different levels.
                    if (tn.tag == Expr.APP && sn.tag == Expr.APP &&
                        sameDeclaration(dtInfo, dsInfo) && tHints >= 0) {
                        emitPhase("lazyDelta.sameDefArgs");
                        // Same definition with Regular hints — identity-based failure cache
                        if (!failedBefore(tn, sn)) {
                            emitPhaseTypes("lazyDelta.sameDefArgs.types", tn, sn);
                            // Try comparing arguments
                            Object[] tLvls = Reducer.constLevels(tnHead);
                            Object[] sLvls = Reducer.constLevels(snHead);
                            if (levelsEq(tLvls, sLvls) && isDefEqArgs(tn, sn)) {
                                return 1; // Equal via argument comparison
                            }
                            cacheFailure(tn, sn);
                        }
                    }
                    emitPhase("lazyDelta.unfoldBoth");
                    // Unfold both
                    Expr unfoldedT = reducer.tryUnfoldDef(tnHead);
                    Expr unfoldedS = reducer.tryUnfoldDef(snHead);
                    if (unfoldedT == null && unfoldedS == null) return lazyDeltaUnknown(tn, sn);
                    if (unfoldedT != null) {
                        tn = reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true);
                    }
                    if (unfoldedS != null) {
                        sn = reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true);
                    }
                    emitDeltaTrace("unfold.both", tn, sn);
                    emitPhasePairStats("lazyDelta.unfoldBoth.stats", tn, sn);
                }
            }

            // Quick check after update (Lean 4 line 996: quick_is_def_eq, use_hash=false default)
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

        return lazyDeltaUnknown(tn, sn); // Iteration limit
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

    /**
     * Lean's `is_eqp(*d_t, *d_s)`: the two heads resolve to the SAME declaration. Lean's
     * environment hands out one canonical constant_info per name, so pointer equality is the
     * faithful test there. Here `env.lookup` re-materializes a declaration whenever its
     * soft-referenced cache entry was collected, so two lookups of one name are routinely
     * different objects — and an identity test then silently disables the same-definition
     * argument shortcut of lazy delta exactly when memory is tight, unfolding both sides
     * instead. `localCohomology.diagramComp` went from 1.6 s to an exhausted 3 GB heap that way.
     */
    private static boolean sameDeclaration(ConstantInfo a, ConstantInfo b) {
        return a == b || (a != null && b != null && a.name.equals(b.name));
    }

    /** Return the delta declaration for a head constant, if it is unfoldable. */
    private ConstantInfo deltaInfo(Expr head) {
        if (head.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookup((Name) head.o0);
        // A definition the reducer's transparency does not unfold is no delta candidate, so lazy
        // delta unfolds the other side instead of giving up (every definition by default).
        return ci != null && ci.getValue() != null && reducer.canUnfold((Name) head.o0) ? ci : null;
    }

    /** Check if head constant is a delta (unfoldable definition). */
    private boolean isDelta(Expr head) {
        return deltaInfo(head) != null;
    }

    /** Get exact reducibility hints: -1 opaque, -2 abbrev, UInt32 regular height. */
    private long getHints(Expr head) {
        if (head.tag != Expr.CONST) return ConstantInfo.HINTS_OPAQUE;
        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null) return ConstantInfo.HINTS_OPAQUE;
        return ci.getHintsCode();
    }

    /**
     * Compare hints for lazy delta. Returns:
     * < 0: unfold t (t has higher height or should be unfolded first)
     * > 0: unfold s
     * = 0: unfold both
     */
    private static int compareHints(long t, long s) {
        if (t == ConstantInfo.REDUCIBILITY_OPAQUE && s == ConstantInfo.REDUCIBILITY_OPAQUE) return 0;
        if (t == ConstantInfo.REDUCIBILITY_OPAQUE) return 1;
        if (s == ConstantInfo.REDUCIBILITY_OPAQUE) return -1;
        if (t == ConstantInfo.REDUCIBILITY_ABBREV && s >= 0) return -1;
        if (s == ConstantInfo.REDUCIBILITY_ABBREV && t >= 0) return 1;
        if (t == ConstantInfo.REDUCIBILITY_ABBREV && s == ConstantInfo.REDUCIBILITY_ABBREV) return 0;
        // Both regular: larger unsigned UInt32 height unfolds first.
        return Long.compare(s, t);
    }

    private static boolean levelsEq(Object[] a, Object[] b) {
        if (a.length != b.length) return false;
        for (int i = 0; i < a.length; i++) {
            if (!Level.eq((Level) a[i], (Level) b[i])) return false;
        }
        return true;
    }

    /** Lean's `t == s` on expr: is_equal, hash-guarded. */
    private static boolean structurallyEqual(Expr t, Expr s) {
        return LeanExprKey.exprEquals(t, s);
    }

    // type_checker.cpp:986-1022 — the pair is stored hash-ordered, looked up symmetrically on a
    // hash tie; one ordered pair, never an equivalence class (lean4#14806).
    private boolean succeededBefore(Expr t, Expr s) {
        int cmp = Integer.compareUnsigned(t.structuralHash(), s.structuralHash());
        if (cmp < 0) return success.contains(t, s);
        if (cmp > 0) return success.contains(s, t);
        return success.contains(t, s) || success.contains(s, t);
    }

    private void cacheSuccess(Expr t, Expr s) {
        if (Integer.compareUnsigned(t.structuralHash(), s.structuralHash()) <= 0) success.add(t, s);
        else success.add(s, t);
    }

    private boolean failedBefore(Expr t, Expr s) {
        int cmp = Integer.compareUnsigned(t.structuralHash(), s.structuralHash());
        if (cmp < 0) return failure.contains(t, s);
        if (cmp > 0) return failure.contains(s, t);
        return failure.contains(t, s) || failure.contains(s, t);
    }

    private void cacheFailure(Expr t, Expr s) {
        if (Integer.compareUnsigned(t.structuralHash(), s.structuralHash()) <= 0) failure.add(t, s);
        else failure.add(s, t);
    }

    /**
     * Lazy delta projection reduction (Lean 4's lazy_delta_proj_reduction).
     * When both sides are projections with the same index, try lazy delta
     * on the struct arguments, then fall back to reduce_proj_core.
     */
    private boolean lazyDeltaProjReduction(Expr tc, Expr sc, long idx) {
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
                tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
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
                sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
                holder[1] = sn;
            }
        } else {
            // Both delta
            long tHints = dtInfo.getHintsCode();
            long sHints = dsInfo.getHintsCode();
            int cmp = compareHints(tHints, sHints);

            if (cmp < 0) {
                Expr unfolded = reducer.tryUnfoldDef(tnHead);
                if (unfolded == null) return 0;
                tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
                holder[0] = tn;
            } else if (cmp > 0) {
                Expr unfolded = reducer.tryUnfoldDef(snHead);
                if (unfolded == null) return 0;
                sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
                holder[1] = sn;
            } else {
                // Same hint level — Lean takes this shortcut when is_delta
                // resolves both sides to the same declaration object, even if
                // the head constants carry syntactically different levels.
                Expr[] tnArgs = (Expr[]) tnFA[1];
                Expr[] snArgs = (Expr[]) snFA[1];
                if (sameDeclaration(dtInfo, dsInfo)
                    && tnArgs.length == snArgs.length
                    && tHints >= 0) { // exact regular height, including zero
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
                    tn = reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true);
                    holder[0] = tn;
                }
                if (unfoldedS != null) {
                    sn = reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true);
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
    private Expr reduceProjCore(Expr c, long idx) {
        Object[] fa = Reducer.getAppFnArgs(c);
        Expr head = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        if (head.tag != Expr.CONST) return null;

        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || !ci.isCtor()) return null;

        return Reducer.projField(ci, args, idx);
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
        } catch (KernelAbort abort) {
            throw abort;
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
        } catch (KernelAbort abort) {
            throw abort;
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
        } catch (KernelAbort abort) {
            throw abort;
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
        } catch (KernelAbort abort) {
            throw abort;
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

    /** Admit an exported inductive block: generate it from the declaration it describes and
     *  compare every record (see {@link InductiveImport}). */
    public static Env checkInductiveBundle(Env env, InductiveBundle bundle, long fuel) {
        return InductiveImport.admit(env, bundle, fuel);
    }


    private static final class ConstantCheckState {
        final TypeChecker tc;
        ConstantCheckState(TypeChecker tc) {
            this.tc = tc;
        }
    }

    /** Set -Dansatz.kernel.cacheReport=true to have every check leave a cacheReport() here. */
    public static volatile java.util.Map<String, Object> lastCacheReport;
    private static final boolean CACHE_REPORT = Boolean.getBoolean("ansatz.kernel.cacheReport");

    /**
     * What the caches hold at the end of a check: entries per cache, and over every term they
     * reference, the number of distinct nodes by identity (what the heap holds) and by
     * structure (what the heap would hold if structurally equal nodes were one object).
     */
    public java.util.Map<String, Object> cacheReport() {
        java.util.LinkedHashMap<String, Object> r = new java.util.LinkedHashMap<>();
        java.util.IdentityHashMap<Expr, Boolean> seenAll = new java.util.IdentityHashMap<>(1 << 20);
        java.util.HashMap<Expr, Boolean> structAll = new java.util.HashMap<>(1 << 20);
        // per cache: [entries, key nodes by identity, key nodes by structure, value nodes by identity, value nodes by structure]
        java.util.function.BiConsumer<String, java.util.List<java.util.List<Expr>>> report = (nm, kv) -> {
            long[] out = new long[4];
            for (int side = 0; side < 2; side++) {
                java.util.IdentityHashMap<Expr, Boolean> seen = new java.util.IdentityHashMap<>(1 << 16);
                java.util.HashMap<Expr, Boolean> struct = new java.util.HashMap<>(1 << 16);
                java.util.ArrayDeque<Expr> stack = new java.util.ArrayDeque<>();
                for (Expr root : kv.get(side)) {
                    stack.push(root);
                    while (!stack.isEmpty()) {
                        Expr e = stack.pop();
                        if (seen.put(e, Boolean.TRUE) != null) continue;
                        struct.put(e, Boolean.TRUE);
                        seenAll.put(e, Boolean.TRUE);
                        structAll.put(e, Boolean.TRUE);
                        switch (e.tag) {
                            case Expr.APP: stack.push((Expr) e.o0); stack.push((Expr) e.o1); break;
                            case Expr.LAM: case Expr.FORALL: stack.push((Expr) e.o1); stack.push((Expr) e.o2); break;
                            case Expr.LET: stack.push((Expr) e.o1); stack.push((Expr) e.o2); stack.push((Expr) e.o3); break;
                            case Expr.MDATA: case Expr.PROJ: stack.push((Expr) e.o1); break;
                            default: break;
                        }
                    }
                }
                out[side * 2] = seen.size(); out[side * 2 + 1] = struct.size();
            }
            r.put(nm, new long[] {kv.get(0).size(), out[0], out[1], out[2], out[3]});
        };
        java.util.function.Function<ExprMap<Expr>, java.util.List<java.util.List<Expr>>> kvOf = m -> {
            java.util.ArrayList<Expr> ks = new java.util.ArrayList<>(m.size()), vs = new java.util.ArrayList<>(m.size());
            m.forEach((k, v) -> { ks.add(k); vs.add((Expr) v); });
            return java.util.List.of(ks, vs);
        };
        java.util.function.Function<ExprPairSet, java.util.List<java.util.List<Expr>>> pairsOf = p -> {
            java.util.ArrayList<Expr> as = new java.util.ArrayList<>(p.size()), bs = new java.util.ArrayList<>(p.size());
            p.forEach((a, b) -> { as.add(a); bs.add(b); });
            return java.util.List.of(as, bs);
        };
        report.accept("infer", kvOf.apply(inferCache));
        report.accept("inferOnly", kvOf.apply(inferOnlyCache));
        report.accept("success", pairsOf.apply(success));
        report.accept("failure", pairsOf.apply(failure));
        for (java.util.Map.Entry<String, ExprMap<Expr>> e : reducer.caches().entrySet()) report.accept(e.getKey(), kvOf.apply(e.getValue()));
        r.put("nodes-by-identity", seenAll.size());
        r.put("nodes-by-structure", structAll.size());
        java.util.HashSet<Integer> hashes = new java.util.HashSet<>(structAll.size() * 2);
        java.util.HashMap<Byte, int[]> byTag = new java.util.HashMap<>();
        for (Expr e : structAll.keySet()) {
            hashes.add(e.hashCode());
            byTag.computeIfAbsent(e.tag, k -> new int[1])[0]++;
        }
        r.put("distinct-hashes", hashes.size());
        // the structural classes with the most identity copies among the cached nodes
        java.util.HashMap<Expr, Integer> copies = new java.util.HashMap<>(structAll.size() * 2);
        for (Expr e : seenAll.keySet()) copies.merge(e, 1, Integer::sum);
        java.util.ArrayList<java.util.Map.Entry<Expr, Integer>> top = new java.util.ArrayList<>(copies.entrySet());
        top.sort((a, b) -> Integer.compare(b.getValue(), a.getValue()));
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < Math.min(25, top.size()); i++) {
            Expr e = top.get(i).getKey();
            sb.append("\n    ").append(top.get(i).getValue()).append("x tag=").append(e.tag)
              .append(" size=").append(exprSize(e, 2000)).append(" ").append(exprFingerprint(e, 4));
        }
        r.put("most-copied", sb.toString());
        return r;
    }

    /**
     * Check one non-inductive, non-quotient declaration against {@code env} the way Lean's
     * environment::add_axiom / add_definition / add_theorem / add_opaque do (environment.cpp),
     * without adding it. Returns the checker that checked the value (or the header), for fuel and
     * statistics.
     */
    private static ConstantCheckState checkConstantPreAdd(Env env, ConstantInfo ci, long fuel,
            Writer traceWriter, boolean phaseTracing) {
        if (ci.isInduct() || ci.isCtor() || ci.isRecursor()) {
            throw new RuntimeException("inductive declarations must be admitted through add_inductive (AddInductive.add, checkInductiveBundle): " + ci.name);
        }
        if (ci.isQuot()) {
            throw new RuntimeException("quotient primitives are admitted through checkConstant: " + ci.name);
        }
        // Share common sub-expressions before type-checking.
        java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>();
        java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>();
        Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
        Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;

        byte safety = admissionSafety(ci);
        TypeChecker tc = newChecker(env, ci, safety, fuel, traceWriter, phaseTracing);
        try {
            if (phaseTracing) tc.emitPhase("checkType");
            checkConstantVal(env, ci, tc, type);
            if (ci.isThm()) {
                if (phaseTracing) tc.emitPhase("isProp");
                if (!tc.isProp(type)) {
                    throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
                }
            }
            if (ci.isAxiom()) return new ConstantCheckState(tc);
            if (ci.isDef() && safety != DEFN_SAFE) {
                // An unsafe or partial definition may refer to itself: Lean checks the header,
                // adds the declaration, then checks the body (add_definition's unsafe branch, and
                // add_mutual for a block of one).
                TypeChecker header = tc;
                tc = newChecker(env.addConstant(ci), ci, safety, fuel, traceWriter, phaseTracing);
                tc.continueFuel(header);   // one budget for the declaration
            }
            checkValue(tc, ci, type, value, phaseTracing);
            return new ConstantCheckState(tc);
        } finally {
            if (CACHE_REPORT) lastCacheReport = tc.cacheReport();
        }
    }

    private static TypeChecker newChecker(Env env, ConstantInfo ci, byte safety, long fuel,
            Writer traceWriter, boolean phaseTracing) {
        TypeChecker tc = new TypeChecker(env, safety, ci.levelParams);
        tc.setFuel(fuel);
        if (traceWriter != null) tc.setTraceWriter(traceWriter);
        tc.setPhaseTracing(phaseTracing);
        return tc;
    }

    /**
     * The checker mode Lean uses for each declaration kind: an axiom is checked as unsafe when it
     * is unsafe; a definition by its own safety; theorems and opaques always as safe
     * (add_theorem and add_opaque construct the default, safe, type_checker).
     */
    private static byte admissionSafety(ConstantInfo ci) {
        if (ci.isDef()) return ci.getDefinitionSafety();
        if (ci.isAxiom() && ci.isUnsafeDeclaration()) return DEFN_UNSAFE;
        return DEFN_SAFE;
    }

    /** Lean's check_constant_val: a fresh name, distinct universe parameters, a closed type that is a type. */
    private static void checkConstantVal(Env env, ConstantInfo ci, TypeChecker tc, Expr type) {
        if (env.lookup(ci.name) != null) {
            throw new RuntimeException("Constant already declared: " + ci.name);
        }
        if (ci.levelParams == null) {
            throw new RuntimeException("Type error: declaration '" + ci.name + "' has no universe parameter list");
        }
        checkDuplicateUnivParams(ci.levelParams, ci.name);
        checkNoMVarNoFVar(ci.name, type);
        tc.ensureSort(tc.check(type));
    }

    /** Lean's check_no_metavar_no_fvar: declarations are closed terms without metavariables. */
    private static void checkNoMVarNoFVar(Name declName, Expr e) {
        if (e.hasMVar()) throw new RuntimeException("Type error: declaration '" + declName + "' has metavariables");
        if (e.hasFVar()) throw new RuntimeException("Type error: declaration '" + declName + "' has free variables");
    }

    /** The value of a definition, theorem or opaque must be present, closed, and of the declared type. */
    private static void checkValue(TypeChecker tc, ConstantInfo ci, Expr type, Expr value, boolean phaseTracing) {
        if (value == null) {
            throw new RuntimeException("Type error: declaration '" + ci.name + "' has no value");
        }
        checkNoMVarNoFVar(ci.name, value);
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

    private static final Object QUOT_BI = clojure.lang.Keyword.intern(null, "default");
    private static Expr qPi(Object nm, Expr dom, Expr body) {
        return Expr.forall(nm, dom, body, QUOT_BI);
    }

    /**
     * Check a quotient primitive. Lean's kernel never accepts quotient declarations from outside:
     * environment::add_quot (quot.cpp) checks the Eq family and generates Quot, Quot.mk, Quot.lift
     * and Quot.ind itself. An exported primitive is therefore admitted only if it is exactly what
     * add_quot generates: a canonical name with its kind, distinct universe parameters, and a type
     * structurally equal (binder names and info aside) to the generated one, with Eq as add_quot
     * requires it.
     */
    public static void checkQuotPrimitive(Env env, ConstantInfo ci) {
        if (env.lookup(ci.name) != null) {
            throw new RuntimeException("Constant already declared: " + ci.name);
        }
        String why = nonCanonicalQuot(ci);
        if (why != null) throw new RuntimeException("Invalid quotient declaration '" + ci.name + "': " + why);
        checkQuotEq(env);
        // add_quot generates the four together; a row given one at a time may only mention
        // primitives already admitted as add_quot generates them (Quot.mk's `Quot` must be the
        // quotient type, not an ordinary declaration of that name).
        java.util.Set<Name> refs = new java.util.HashSet<>();
        quotRefs(ci.type, refs);
        refs.remove(ci.name);
        for (Name ref : refs) {
            ConstantInfo r = env.lookup(ref);
            if (r == null || nonCanonicalQuot(r) != null) {
                throw new RuntimeException("Invalid quotient declaration '" + ci.name + "': refers to " + ref +
                    ", which is not an admitted quotient primitive");
            }
        }
    }

    /** Why ci is not the primitive add_quot generates under its name, or null if it is. */
    private static String nonCanonicalQuot(ConstantInfo ci) {
        Object kind = QUOT_KINDS.get(ci.name);
        if (!ci.isQuot() || kind == null || !kind.equals(ci.quotKind)) {
            return "not a canonical quotient primitive (Quot / Quot.mk / Quot.lift / Quot.ind) of its kind";
        }
        if (ci.levelParams == null || new java.util.HashSet<>(java.util.Arrays.asList(ci.levelParams)).size() != ci.levelParams.length) {
            return "universe parameters are not distinct";
        }
        Expr expected = expectedQuotType((Name) ci.name, ci.levelParams);
        if (expected == null || !LeanExprKey.exprEquals(ci.type, expected)) {
            return "type is not the one the kernel generates for this quotient primitive";
        }
        return null;
    }

    /** The quotient primitives a (generated, binder/app/sort/const) quotient type mentions. */
    private static void quotRefs(Expr e, java.util.Set<Name> out) {
        if (e.tag == Expr.CONST) {
            if (QUOT_KINDS.containsKey(e.o0)) out.add((Name) e.o0);
            return;
        }
        if (e.o0 instanceof Expr) quotRefs((Expr) e.o0, out);
        if (e.o1 instanceof Expr) quotRefs((Expr) e.o1, out);
        if (e.o2 instanceof Expr) quotRefs((Expr) e.o2, out);
        if (e.o3 instanceof Expr) quotRefs((Expr) e.o3, out);
    }

    /**
     * Whether env holds (visibly) the four primitives add_quot generates. Quotient reduction
     * relies on it, so it is derived from the declarations themselves rather than from how they
     * were admitted or loaded.
     */
    static boolean hasQuotPackage(Env env) {
        for (Name n : QUOT_KINDS.keySet()) {
            ConstantInfo q = env.lookup(n);
            if (q == null || nonCanonicalQuot(q) != null) return false;
        }
        return true;
    }

    private static final java.util.Map<Name, Object> QUOT_KINDS = java.util.Map.of(
        Name.QUOT, clojure.lang.Keyword.intern(null, "type"),
        Name.QUOT_MK, clojure.lang.Keyword.intern(null, "ctor"),
        Name.QUOT_LIFT, clojure.lang.Keyword.intern(null, "lift"),
        Name.QUOT_IND, clojure.lang.Keyword.intern(null, "ind"));

    /** Lean's check_eq_type (quot.cpp): Eq.{u} : {α : Sort u} → α → α → Prop with the one constructor Eq.refl. */
    public static void checkQuotEq(Env env) {
        ConstantInfo eq = env.lookup(Name.EQ);
        if (eq == null || !eq.isInduct() || eq.levelParams.length != 1 || eq.ctors == null || eq.ctors.length != 1) {
            throw new RuntimeException("failed to initialize quot module, environment does not have the expected 'Eq' type");
        }
        Expr PROP = Expr.sort(Level.ZERO_LEVEL, false);
        Level u = Level.param(eq.levelParams[0]);
        // {α : Sort u} → α → α → Prop
        Expr eqType = qPi("α", Expr.sort(u, true), qPi("a", Expr.bvar(0), qPi("b", Expr.bvar(1), PROP)));
        if (!LeanExprKey.exprEquals(eq.type, eqType)) {
            throw new RuntimeException("failed to initialize quot module, 'Eq' has an unexpected type");
        }
        ConstantInfo refl = env.lookup(eq.ctors[0]);
        if (refl == null || !refl.isCtor() || refl.levelParams.length != 1) {
            throw new RuntimeException("failed to initialize quot module, unexpected 'Eq' constructor");
        }
        Level v = Level.param(refl.levelParams[0]);
        // {α : Sort v} → (a : α) → @Eq.{v} α a a
        Expr reflType = qPi("α", Expr.sort(v, true), qPi("a", Expr.bvar(0),
            Expr.app(Expr.app(Expr.app(Expr.mkConst(Name.EQ, new Object[]{v}, true), Expr.bvar(1)), Expr.bvar(0)), Expr.bvar(0))));
        if (!LeanExprKey.exprEquals(refl.type, reflType)) {
            throw new RuntimeException("failed to initialize quot module, unexpected type for 'Eq' type constructor");
        }
    }

    /** Admit a checked quotient primitive; the module is initialized once the package is complete. */
    private static Env addQuotPrimitive(Env env, ConstantInfo ci) {
        Env added = env.addConstant(ci);
        return hasQuotPackage(added) ? added.enableQuot() : added;
    }

    /** Kernel-expected type for a canonical quotient primitive, or null if the name/arity is not canonical. */
    private static Expr expectedQuotType(Name name, Object[] lps) {
        Expr PROP = Expr.sort(Level.ZERO_LEVEL, false);
        // r : α → α → Prop, built at the binder site directly below α (α = bvar 0 there).
        Expr rel = qPi("a", Expr.bvar(0), qPi("a", Expr.bvar(1), PROP));
        if (name == Name.QUOT || name == Name.QUOT_MK || name == Name.QUOT_IND) {
            if (lps.length != 1) return null;
            Level u = Level.param(lps[0]);
            Expr Su = Expr.sort(u, true);
            Expr QuotU = Expr.mkConst(Name.QUOT, new Object[]{u}, true);
            if (name == Name.QUOT) {
                // ∀ (α : Sort u) (r : α→α→Prop), Sort u
                return qPi("a", Su, qPi("r", rel, Su));
            }
            if (name == Name.QUOT_MK) {
                // ∀ (α : Sort u) (r : α→α→Prop) (a : α), @Quot.{u} α r
                Expr res = Expr.app(Expr.app(QuotU, Expr.bvar(2)), Expr.bvar(1));
                return qPi("a", Su, qPi("r", rel, qPi("a", Expr.bvar(1), res)));
            }
            // Quot.ind: ∀ α r (β : @Quot α r → Prop) (h : ∀ a, β (@Quot.mk α r a)) (q : @Quot α r), β q
            Expr QuotMkU = Expr.mkConst(Name.QUOT_MK, new Object[]{u}, true);
            Expr betaType = qPi("q", Expr.app(Expr.app(QuotU, Expr.bvar(1)), Expr.bvar(0)), PROP);
            Expr hType = qPi("a", Expr.bvar(2),
                Expr.app(Expr.bvar(1),
                    Expr.app(Expr.app(Expr.app(QuotMkU, Expr.bvar(3)), Expr.bvar(2)), Expr.bvar(0))));
            Expr qType = Expr.app(Expr.app(QuotU, Expr.bvar(3)), Expr.bvar(2));
            Expr res = Expr.app(Expr.bvar(2), Expr.bvar(0));
            return qPi("a", Su, qPi("r", rel, qPi("b", betaType, qPi("h", hType, qPi("q", qType, res)))));
        }
        if (name == Name.QUOT_LIFT) {
            if (lps.length != 2) return null;
            Level u = Level.param(lps[0]);
            Level v = Level.param(lps[1]);
            Expr Su = Expr.sort(u, true);
            Expr Sv = Expr.sort(v, true);
            Expr QuotU = Expr.mkConst(Name.QUOT, new Object[]{u}, true);
            Expr EqV = Expr.mkConst(Name.EQ, new Object[]{v}, true);
            // f : α → β   (ctx [α,r,β])
            Expr fType = qPi("a", Expr.bvar(2), Expr.bvar(1));
            // h : ∀ (a b : α), r a b → @Eq.{v} β (f a) (f b)   (ctx [α,r,β,f])
            Expr rab = Expr.app(Expr.app(Expr.bvar(4), Expr.bvar(1)), Expr.bvar(0));
            Expr eqBody = Expr.app(Expr.app(Expr.app(EqV, Expr.bvar(4)),
                Expr.app(Expr.bvar(3), Expr.bvar(2))),
                Expr.app(Expr.bvar(3), Expr.bvar(1)));
            Expr hType = qPi("a", Expr.bvar(3), qPi("b", Expr.bvar(4), qPi("h", rab, eqBody)));
            // q : @Quot.{u} α r   (ctx [α,r,β,f,h])
            Expr qType = Expr.app(Expr.app(QuotU, Expr.bvar(4)), Expr.bvar(3));
            // result : β   (ctx [α,r,β,f,h,q])
            return qPi("a", Su, qPi("r", rel, qPi("b", Sv, qPi("f", fType, qPi("h", hType, qPi("q", qType, Expr.bvar(3)))))));
        }
        return null;
    }

    public static Env checkConstant(Env env, ConstantInfo ci, long fuel) {
        // Quotient primitives are trusted kernel primitives, not externally type-checked
        // declarations — but we MUST validate they are the canonical Quot/Quot.mk/Quot.lift/
        // Quot.ind with the expected types before admitting (Lean generates these internally).
        if (ci.isQuot()) {
            checkQuotPrimitive(env, ci);
            return addQuotPrimitive(env, ci);
        }
        checkConstantPreAdd(env, ci, fuel, null, false);
        return env.addConstant(ci);
    }

    /**
     * Admit a group of unsafe/partial definitions that may refer to each other (and to
     * themselves), following Lean 4's {@code environment::add_mutual} (and the unsafe branch of
     * {@code add_definition}, which is the one-member case): every member must carry the SAME
     * non-safe safety; the headers are checked in {@code env}, all members are added, and only
     * then are the bodies checked — in the extended environment, so recursive references resolve.
     * This is how Lean admits the {@code _unsafe_rec} companions of {@code partial} / compiled
     * well-founded definitions. Safe definitions never take this path.
     */
    public static Env checkMutualDefinitions(Env env, java.util.List<ConstantInfo> cis, long fuel) {
        if (cis.isEmpty()) throw new RuntimeException("invalid empty mutual definition");
        byte safety = cis.get(0).getDefinitionSafety();
        Object[] levelParams = cis.get(0).levelParams;
        if (safety == DEFN_SAFE)
            throw new RuntimeException("invalid mutual definition, declaration is not tagged as unsafe/partial: " + cis.get(0).name);
        TypeChecker prev = null;   // the block is one declaration: one fuel budget across its checkers
        for (ConstantInfo ci : cis) {
            if (!ci.isDef()) throw new RuntimeException("invalid mutual definition, not a definition: " + ci.name);
            if (ci.getDefinitionSafety() != safety)
                throw new RuntimeException("invalid mutual definition, declarations must have the same safety annotation: " + ci.name);
            // Lean environment::add_mutual compares the ordered universe-parameter lists,
            // before checking headers; each member being well formed individually is insufficient.
            if (!java.util.Arrays.equals(levelParams, ci.levelParams))
                throw new RuntimeException("invalid mutual definition, declarations must have the same universe level parameters: " + ci.name);
            prev = budgeted(new TypeChecker(env, safety, ci.levelParams), prev, fuel);
            checkConstantVal(env, ci, prev, Expr.shareCommon(ci.type));
        }
        Env newEnv = env;
        for (ConstantInfo ci : cis) newEnv = newEnv.addConstant(ci);
        for (ConstantInfo ci : cis) {
            TypeChecker tc = prev = budgeted(new TypeChecker(newEnv, safety, ci.levelParams), prev, fuel);
            checkValue(tc, ci, Expr.shareCommon(ci.type),
                       ci.value != null ? Expr.shareCommon(ci.value) : null, false);
        }
        return newEnv;
    }

    private static TypeChecker budgeted(TypeChecker tc, TypeChecker prev, long fuel) {
        if (prev == null) tc.setFuel(fuel); else tc.continueFuel(prev);
        return tc;
    }

    /** Type-check a declaration with structured NDJSON trace output. */
    public static Env checkConstantTraced(Env env, ConstantInfo ci, long fuel, Writer traceWriter) {
        if (ci.isQuot()) {
            checkQuotPrimitive(env, ci);
            return addQuotPrimitive(env, ci);
        }
        checkConstantPreAdd(env, ci, fuel, traceWriter, false);
        try { traceWriter.flush(); } catch (IOException e) {}
        return env.addConstant(ci);
    }

    /** Like checkConstantTraced, but emits simple phase markers for theorem/definition checking. */
    public static Env checkConstantTracedPhased(Env env, ConstantInfo ci, long fuel, Writer traceWriter) {
        if (ci.isQuot()) {
            checkQuotPrimitive(env, ci);
            return addQuotPrimitive(env, ci);
        }
        checkConstantPreAdd(env, ci, fuel, traceWriter, true);
        try { traceWriter.flush(); } catch (IOException e) { throw new RuntimeException(e); }
        return env.addConstant(ci);
    }

    private static final String[] EMPTY_REDUCER_TRACE = new String[0];

    /**
     * Type-check and return fuel used. For instrumentation.
     */
    public static long checkConstantFuel(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            checkQuotPrimitive(env, ci);
            return 0;
        }
        return checkConstantPreAdd(env, ci, fuel, null, false).tc.getFuelUsed();
    }

    /**
     * Type-check and return detailed stats (counters + trace).
     * Returns Object[4]: [fuelUsed (Long), stats (HashMap), trace (String[]), errorOrNull].
     */
    public static Object[] checkConstantFuelStats(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            try {
                checkQuotPrimitive(env, ci);
                return new Object[]{0L, new HashMap<String, Long>(), EMPTY_REDUCER_TRACE, null};
            } catch (RuntimeException ex) {
                return new Object[]{0L, new HashMap<String, Long>(), EMPTY_REDUCER_TRACE, ex.getMessage()};
            }
        }
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
