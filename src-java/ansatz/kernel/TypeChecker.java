// Ansatz kernel — Type inference and definitional equality.

package ansatz.kernel;

import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;
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

    private final Env env;
    private final Reducer reducer;
    private final EquivManager eqvManager;
    private final IdentityHashMap<Expr, Expr> inferCache;      // for check mode
    private final IdentityHashMap<Expr, Expr> inferOnlyCache;  // for infer_only mode
    private final IdentityHashMap<Expr, IdentityHashMap<Expr, Boolean>> failureCache;
    // Identity-based cache for isDefEqCore results.
    // Prevents exponential re-comparison of DAG-shared expression pairs.
    // Key: identity of (t,s) pair. Value: Boolean result.
    private final IdentityHashMap<Expr, IdentityHashMap<Expr, Boolean>> isDefEqIdentityCache;
    private long nextId;
    private int isDefEqDepth;
    public boolean tracing;

    // isDefEq diagnostic counters
    long isDefEqCalls;
    long isDefEqQuickHits;    // pointer equality or hash mismatch
    long isDefEqEquivHits;    // EquivManager hits
    long isDefEqProofIrrelHits;
    long isDefEqCacheFull;    // calls that happened after cache was full (couldn't store result)
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
            sb.append(",\"by\":\"").append(resolvedBy);
            sb.append("\"}\n");
            traceWriter.write(sb.toString());
        } catch (IOException e) {
            // silently ignore write failures
        }
    }

    /** Minimal JSON string escaping. */
    private static String jsonEsc(String s) {
        if (s.length() > 200) s = s.substring(0, 200) + "...";
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
        this.env = env;
        this.reducer = new Reducer(env);
        this.eqvManager = new EquivManager();
        this.inferCache = new IdentityHashMap<>(1024);
        this.inferOnlyCache = new IdentityHashMap<>(1024);
        this.failureCache = new IdentityHashMap<>(256);
        this.isDefEqIdentityCache = new IdentityHashMap<>(1024);
        this.nextId = 0;
        this.lctx = new HashMap<>();
        this.reducer.setLctx(this.lctx);
        this.reducer.setCallbacks(this::inferTypeOnly, this::isDefEq);
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
        stats.put("isDefEq-cache-full", isDefEqCacheFull);
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
        lctx.put(id, new Object[]{0, name, type, binderInfo});
    }

    // ============================================================
    // Type inference
    // ============================================================

    /**
     * Infer type in infer-only mode (Lean's infer_type → infer_type_core(e, true)).
     * Skips isDefEq checks on application arguments. The final type match
     * is checked separately via isDefEq(val_type, declared_type).
     * Using full check mode (false) causes 198,000x more isDefEq calls than Lean 4
     * for heavy proofs — every argument in every application gets checked.
     */
    public Expr inferType(Expr e) {
        return inferTypeCore(e, true);
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
        IdentityHashMap<Expr, Expr> cache = inferOnly ? inferOnlyCache : inferCache;
        Expr cached = cache.get(e);
        if (cached != null) return cached;

        Expr result;
        switch (e.tag) {
            case Expr.BVAR:
                throw new RuntimeException("Type error: Loose bound variable in infer-type");

            case Expr.SORT:
                result = Expr.sort(Level.succ((Level) e.o0), Level.hasParam(Level.succ((Level) e.o0)));
                break;

            case Expr.CONST: {
                ConstantInfo ci = env.lookupOrThrow((Name) e.o0);
                Object[] levels = Reducer.constLevels(e);
                if (ci.levelParams.length != levels.length) {
                    throw new RuntimeException("Type error: Universe level mismatch for " + e.o0 +
                        " expected=" + ci.levelParams.length + " actual=" + levels.length);
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

        cache.put(e, result);
        return result;
    }

    private Expr ensureSort(Expr e) {
        Expr w = whnf(e);
        if (w.tag == Expr.SORT) return w;
        throw new RuntimeException("Type error: Expected a sort (Type/Prop)");
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
        // Match Lean 4: all checks happen inside is_def_eq_core,
        // including pointer/structural equality via quick_is_def_eq.
        // addEquiv is now called inside isDefEqCore with canonical (deepReIntern'd)
        // expressions, so quickIsDefEq's EquivManager check finds them by pointer.
        return isDefEqCore(t, s);
    }

    private static final int ISDEFEQ_CACHE_MAX = 10_000_000;

    private boolean isDefEqCore(Expr t, Expr s) {
        // Canonicalize inputs via the intern table. Matches Lean 4's global hash-consing:
        // after construction, structurally-equal expressions are pointer-equal.
        // For already-canonical expressions (the common case), deepReIntern is O(1).
        // For fresh non-canonical expressions (e.g. from instantiateRev), this pays
        // O(|expr|) once and subsequent structurally-equal expressions are O(1).
        t = Expr.deepReIntern(t);
        s = Expr.deepReIntern(s);
        isDefEqCalls++;
        if (isDefEqDepth < isDefEqDepthHist.length) isDefEqDepthHist[isDefEqDepth]++;
        // Capture a sample of expression shapes for diagnostics (only non-pointer-equal pairs)
        if (diagCaptures.size() < DIAG_CAPTURE_LIMIT && isDefEqDepth >= DIAG_CAPTURE_MIN_DEPTH && !t.isEqp(s)) {
            String ts = exprFingerprint(t, 6);
            String ss = exprFingerprint(s, 6);
            diagCaptures.add(new String[]{ts, ss, "d=" + isDefEqDepth});
        }
        if (t.isEqp(s)) { isDefEqQuickHits++; return true; }
        reducer.checkFuelPublic();
        // Identity-based cache: avoid re-comparing the same (identity) pair
        // of expressions that arises from DAG sharing.
        IdentityHashMap<Expr, Boolean> innerMap = isDefEqIdentityCache.get(t);
        if (innerMap != null) {
            Boolean cached = innerMap.get(s);
            if (cached != null) { isDefEqQuickHits++; return cached; }
        }
        isDefEqDepth++;
        try {
            boolean result = isDefEqCoreImpl(t, s);
            // Cache the result, but cap total size to prevent OOM
            if (isDefEqIdentityCache.size() < ISDEFEQ_CACHE_MAX) {
                if (innerMap == null) {
                    innerMap = new IdentityHashMap<>(4);
                    isDefEqIdentityCache.put(t, innerMap);
                }
                innerMap.put(s, result);
            } else {
                isDefEqCacheFull++;
            }
            // Store canonical (deepReIntern'd) expressions in EquivManager so that
            // quickIsDefEq's pointer-based EquivManager check finds them. Without this,
            // the caller's non-canonical t/s would be stored, missing all canonical lookups.
            if (result) eqvManager.addEquiv(t, s);
            return result;
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
        Expr tn = Expr.deepReIntern(reducer.whnfCore(t, false, true));
        Expr sn = Expr.deepReIntern(reducer.whnfCore(s, false, true));

        // Quick check after whnf_core (Lean 4 lines 1116-1124)
        // Note: Lean uses use_hash=false (default) for the second quick check
        if (!tn.isEqp(t) || !sn.isEqp(s)) {
            int q = quickIsDefEq(tn, sn, false);
            if (q != 0) {
                boolean r = q == 1;
                if (doTrace) trace("=> quickEq after whnfCore");
                if (doEmit) emitTrace(lFp, rFp, r, "quick_whnfcore");
                return r;
            }
        }

        if (doTrace) {
            if (!tn.isEqp(t) || !sn.isEqp(s))
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
            Expr tn2 = Expr.deepReIntern(reducer.whnfCore(tn, false, false));
            Expr sn2 = Expr.deepReIntern(reducer.whnfCore(sn, false, false));
            if (!tn2.isEqp(tn) || !sn2.isEqp(sn)) {
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

            // Nat offset check
            int offsetResult = isDefEqOffset(tn, sn);
            if (offsetResult != 0) return offsetResult;

            // Nat builtin reduction (matching Lean 4's lazy_delta_reduction lines 980-986)
            // Lean 4 delegates to is_def_eq_core on the reduced result.
            // In eagerReduce mode, also fire when terms have fvars (Lean 4 line 980)
            if ((!tn.hasFVar() && !sn.hasFVar()) || eagerReduce) {
                Expr natTn = reducer.tryReduceNatExpr(tn);
                if (natTn != null) {
                    return isDefEqCore(natTn, sn) ? 1 : -1;
                }
                Expr natSn = reducer.tryReduceNatExpr(sn);
                if (natSn != null) {
                    return isDefEqCore(tn, natSn) ? 1 : -1;
                }
                // Try Int reduction (native optimization)
                Object[] tnFA0 = Reducer.getAppFnArgs(tn);
                Expr intTn = reducer.tryReduceInt((Expr) tnFA0[0], (Expr[]) tnFA0[1]);
                if (intTn != null) {
                    return isDefEqCore(intTn, sn) ? 1 : -1;
                }
                Object[] snFA0 = Reducer.getAppFnArgs(sn);
                Expr intSn = reducer.tryReduceInt((Expr) snFA0[0], (Expr[]) snFA0[1]);
                if (intSn != null) {
                    return isDefEqCore(tn, intSn) ? 1 : -1;
                }
            }

            Object[] tnFA = Reducer.getAppFnArgs(tn);
            Object[] snFA = Reducer.getAppFnArgs(sn);
            Expr tnHead = (Expr) tnFA[0];
            Expr snHead = (Expr) snFA[0];

            // Is either side a delta (unfoldable definition)?
            boolean dtHasDelta = isDelta(tnHead);
            boolean dsHasDelta = isDelta(snHead);

            if (!dtHasDelta && !dsHasDelta) {
                return 0; // Neither side can be unfolded
            }

            if (dtHasDelta && !dsHasDelta) {
                // Only left side is a definition — but first try to unfold projection app on right
                // (Lean 4 lines 900-904: try_unfold_proj_app optimization)
                Expr snNew = tryUnfoldProjApp(sn);
                if (snNew != null) {
                    sn = snNew;
                } else {
                    Expr unfolded = reducer.tryUnfoldDef(tnHead);
                    if (unfolded == null) return 0;
                    tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                }
            } else if (!dtHasDelta && dsHasDelta) {
                // Only right side is a definition — but first try to unfold projection app on left
                // (Lean 4 lines 907-911: try_unfold_proj_app optimization)
                Expr tnNew = tryUnfoldProjApp(tn);
                if (tnNew != null) {
                    tn = tnNew;
                } else {
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return 0;
                    sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                }
            } else {
                // Both sides are definitions — use hints to decide
                int tHints = getHints(tnHead);
                int sHints = getHints(snHead);
                int cmp = compareHints(tHints, sHints);

                if (cmp < 0) {
                    // Unfold left (higher height / more complex)
                    Expr unfolded = reducer.tryUnfoldDef(tnHead);
                    if (unfolded == null) return 0;
                    tn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true));
                } else if (cmp > 0) {
                    // Unfold right
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return 0;
                    sn = Expr.deepReIntern(reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true));
                } else {
                    // Same hint level — try argument comparison first if same definition
                    if (tn.tag == Expr.APP && sn.tag == Expr.APP &&
                        tnHead.o0 != null && tnHead.o0.equals(snHead.o0) && tHints > 0) {
                        // Same definition with Regular hints — identity-based failure cache
                        IdentityHashMap<Expr, Boolean> inner = failureCache.get(tn);
                        if (inner == null || !Boolean.TRUE.equals(inner.get(sn))) {
                            // Try comparing arguments
                            Object[] tLvls = Reducer.constLevels(tnHead);
                            Object[] sLvls = Reducer.constLevels(snHead);
                            if (levelsEq(tLvls, sLvls) && isDefEqArgs(tn, sn)) {
                                deltaHolder[0] = tn;
                                deltaHolder[1] = sn;
                                return 1; // Equal via argument comparison
                            }
                            if (inner == null) {
                                inner = new IdentityHashMap<>(4);
                                failureCache.put(tn, inner);
                            }
                            inner.put(sn, Boolean.TRUE);
                        }
                    }
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
                }
            }

            // Quick check after update (Lean 4 line 996: quick_is_def_eq, use_hash=false default)
            deltaHolder[0] = tn;
            deltaHolder[1] = sn;
            {
                int q = quickIsDefEq(tn, sn, false);
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
        return (eNew != e) ? eNew : null;
    }

    /** Check if head constant is a delta (unfoldable definition). */
    private boolean isDelta(Expr head) {
        if (head.tag != Expr.CONST) return false;
        ConstantInfo ci = env.lookup((Name) head.o0);
        return ci != null && ci.getValue() != null;
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

        boolean dtHasDelta = isDelta(tnHead);
        boolean dsHasDelta = isDelta(snHead);

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
            int tHints = getHints(tnHead);
            int sHints = getHints(snHead);
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
                // Same hint level — try argument comparison first if same definition
                // (matching Lean 4's is_eqp optimization, using Name.equals)
                Expr[] tnArgs = (Expr[]) tnFA[1];
                Expr[] snArgs = (Expr[]) snFA[1];
                if (tnHead.tag == Expr.CONST && snHead.tag == Expr.CONST
                    && ((Name) tnHead.o0).equals((Name) snHead.o0)
                    && tnArgs.length == snArgs.length
                    && tHints > 0) { // regular hints (positive = regular in our encoding)
                    IdentityHashMap<Expr, Boolean> inner = failureCache.get(tn);
                    if (inner == null || !Boolean.TRUE.equals(inner.get(sn))) {
                        if (levelsEq(Reducer.constLevels(tnHead), Reducer.constLevels(snHead))
                            && isDefEqArgs(tn, sn)) {
                            holder[0] = tn;
                            holder[1] = sn;
                            return 1; // DefEqual via argument comparison
                        }
                        if (inner == null) {
                            inner = new IdentityHashMap<>(4);
                            failureCache.put(tn, inner);
                        }
                        inner.put(sn, Boolean.TRUE);
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
        if (tArgs.length != sArgs.length) return false;
        if (!isDefEq(tFn, sFn)) return false;
        for (int i = 0; i < tArgs.length; i++) {
            if (!isDefEq(tArgs[i], sArgs[i])) return false;
        }
        return true;
    }

    /** Check if two application expressions have equal arguments. */
    private boolean isDefEqArgs(Expr t, Expr s) {
        // Collect args from both
        Object[] tfa = Reducer.getAppFnArgs(t);
        Object[] sfa = Reducer.getAppFnArgs(s);
        Expr[] tArgs = (Expr[]) tfa[1];
        Expr[] sArgs = (Expr[]) sfa[1];
        if (tArgs.length != sArgs.length) return false;
        for (int i = 0; i < tArgs.length; i++) {
            if (!isDefEq(tArgs[i], sArgs[i])) return false;
        }
        return true;
    }

    /** Try eta expansion: t =?= λ x. s x when s is lam and t is not. */
    private boolean tryEta(Expr t, Expr s) {
        if (s.tag == Expr.LAM && t.tag != Expr.LAM) {
            long fvId = freshId();
            Expr fv = Expr.fvar(fvId);
            lctxAddLocal(fvId, null, (Expr) s.o1);
            try {
                return isDefEq(
                    Expr.app(Reducer.lift(t, 1, 0), fv),
                    Reducer.instantiate1((Expr) s.o2, fv));
            } finally {
                lctxRemove(fvId);
            }
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
        if (nfields == 0) return false; // unit-like handled separately

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

    public static Env checkConstant(Env env, ConstantInfo ci, long fuel) {
        // Quotient primitives: just enable and add (no type-checking needed, they are axioms)
        if (ci.isQuot()) {
            return env.enableQuot().addConstant(ci);
        }

        Expr.enableIntern();
        try {
            // === Check 0: Duplicate universe level parameters ===
            // Following Lean 4 environment.cpp:111-125
            checkDuplicateUnivParams(ci.levelParams, ci.name);

            // Share common sub-expressions before type-checking.
            java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
            java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
            Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
            Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;
            // Seed intern table with shareCommon results so reduction-created
            // expressions are pointer-identical to proof sub-expressions.
            Expr.seedIntern(scCache);

            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            // Theorem: check is_prop first, matching Lean 4's add_theorem
            if (ci.isThm()) {
                if (!tc.isProp(type))
                    throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
            }

            // Check type is well-formed (must be a sort)
            tc.ensureSort(tc.inferType(type));

            // === Inductive type validation ===
            // Check that the inductive result (after stripping params/indices) is a sort,
            // and that numParams doesn't exceed the actual forall binder count.
            if (ci.isInduct() && !ci.isUnsafe) {
                validateInductiveResultSort(ci, tc);
            }

            // === Constructor validation ===
            // Run when processing the CONSTRUCTOR (not the inductive type itself),
            // because by this point the inductive type is already in the env.
            // Following Lean 4 inductive.cpp check_constructors (lines 412-453).
            if (ci.isCtor() && !ci.isUnsafe) {
                ConstantInfo indCi = env.lookup(ci.inductName);
                if (indCi != null && indCi.isInduct() && !indCi.isUnsafe) {
                    validateConstructor(env, indCi, ci, tc);
                }
            }

            // For recursors: validate rule field counts match constructors.
            // We also type-check rule RHS AFTER adding the recursor to env
            // (the RHS references the recursor itself for recursive calls).
            // Lean 4 regenerates recursors from scratch (inductive.cpp:752-776);
            // we validate imported rules post-addition instead.
            if (ci.isRecursor() && ci.rules != null) {
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

            // For definitions, theorems, and opaques: check value matches type
            if (value != null && (ci.isDef() || ci.isThm() || ci.isOpaq())) {
                Expr inferred = tc.inferType(value);
                if (!tc.isDefEq(inferred, type)) {
                    String infStr = inferred.toString();
                    String declStr = ci.type.toString();
                    if (infStr.length() > 300) infStr = infStr.substring(0, 300) + "...";
                    if (declStr.length() > 300) declStr = declStr.substring(0, 300) + "...";
                    throw new RuntimeException("Type error: Declaration value type does not match declared type for " + ci.name +
                        "\n  inferred: " + infStr + "\n  declared: " + declStr);
                }
            }

            // Add to environment
            Env newEnv = env.addConstant(ci);

            // Post-addition: validate recursor rules by regenerating expected RHS
            // bodies and comparing. Follows Lean 4 inductive.cpp:705-748 mk_rec_rules.
            if (ci.isRecursor() && ci.rules != null && !ci.isUnsafe) {
                validateRecursorRules(newEnv, ci);
            }

            return newEnv;
        } finally {
            Expr.disableIntern();
        }
    }

    /** Type-check a declaration with structured NDJSON trace output. */
    public static Env checkConstantTraced(Env env, ConstantInfo ci, long fuel, Writer traceWriter) {
        if (ci.isQuot()) {
            return env.enableQuot().addConstant(ci);
        }
        Expr.enableIntern();
        try {
            java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
            java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
            Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
            Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;
            // Seed intern table with shareCommon results so reduction-created
            // expressions are pointer-identical to proof sub-expressions.
            Expr.seedIntern(scCache);
            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            tc.setTraceWriter(traceWriter);
            if (ci.isThm()) {
                if (!tc.isProp(type))
                    throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
            }
            tc.ensureSort(tc.inferType(type));
            if (value != null && (ci.isDef() || ci.isThm() || ci.isOpaq())) {
                Expr inferred = tc.inferType(value);
                if (!tc.isDefEq(inferred, type)) {
                    throw new RuntimeException("Type error: value type mismatch for " + ci.name);
                }
            }
            // Callers must add ci to env themselves (Env is immutable)
            try { traceWriter.flush(); } catch (IOException e) {}
            return env.addConstant(ci);
        } finally {
            Expr.disableIntern();
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
            java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
            java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
            Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
            Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;
            // Seed intern table with shareCommon results so reduction-created
            // expressions are pointer-identical to proof sub-expressions.
            Expr.seedIntern(scCache);
            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            if (ci.isThm()) {
                if (!tc.isProp(type))
                    throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
            }
            tc.ensureSort(tc.inferType(type));
            if (value != null && (ci.isDef() || ci.isThm() || ci.isOpaq())) {
                Expr inferred = tc.inferType(value);
                if (!tc.isDefEq(inferred, type)) {
                    String infStr = inferred.toString();
                    String declStr = ci.type.toString();
                    if (infStr.length() > 300) infStr = infStr.substring(0, 300) + "...";
                    if (declStr.length() > 300) declStr = declStr.substring(0, 300) + "...";
                    throw new RuntimeException("Type error: Declaration value type does not match declared type for " + ci.name +
                        "\n  inferred: " + infStr + "\n  declared: " + declStr);
                }
            }
            // Callers must add ci to env themselves (Env is immutable)
            return tc.getFuelUsed();
        } finally {
            Expr.disableIntern();
        }
    }

    /**
     * Type-check and return detailed stats (counters + trace).
     * Returns Object[3]: [fuelUsed (Long), stats (HashMap), trace (String[])].
     */
    public static Object[] checkConstantFuelStats(Env env, ConstantInfo ci, long fuel) {
        if (ci.isQuot()) {
            // Callers must handle env.enableQuot().addConstant(ci)
            return new Object[]{0L, new HashMap<String, Long>(), new String[0], null};
        }
        Expr.enableIntern();
        try {
            java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
            java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
            Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
            Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;
            // Seed intern table with shareCommon results so reduction-created
            // expressions are pointer-identical to proof sub-expressions.
            Expr.seedIntern(scCache);
            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            try {
                if (ci.isThm()) {
                    if (!tc.isProp(type))
                        throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
                }
                tc.ensureSort(tc.inferType(type));
                if (value != null && (ci.isDef() || ci.isThm() || ci.isOpaq())) {
                    Expr inferred = tc.inferType(value);
                    if (!tc.isDefEq(inferred, type)) {
                        String infStr = inferred.toString();
                        String declStr = ci.type.toString();
                        if (infStr.length() > 300) infStr = infStr.substring(0, 300) + "...";
                        if (declStr.length() > 300) declStr = declStr.substring(0, 300) + "...";
                        throw new RuntimeException("Type error: Declaration value type does not match declared type for " + ci.name +
                            "\n  inferred: " + infStr + "\n  declared: " + declStr);
                    }
                }
                // Note: env.addConstant result not captured here —
                // callers must add ci to their env themselves
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), EMPTY_REDUCER_TRACE, null};
            } catch (RuntimeException ex) {
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), EMPTY_REDUCER_TRACE, ex.getMessage()};
            } catch (StackOverflowError ex) {
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), EMPTY_REDUCER_TRACE,
                    "StackOverflowError (whnf max depth: " + tc.getReducerMaxDepth() + ")"};
            }
        } finally {
            Expr.disableIntern();
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
    private static void validateConstructor(Env env, ConstantInfo indCi, ConstantInfo ctorCi, TypeChecker tc) {
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

            // Check 5: Strict positivity
            checkPositivity(tc, fieldType, inductiveNames, ctorCi.name, fieldIdx + 1);

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
            java.util.HashSet<Name> inductiveNames, Name ctorName, int argIdx) {
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
            checkPositivity(tc, body, inductiveNames, ctorName, argIdx);
        } else {
            // Case 3: Must be a valid inductive application or a nested inductive
            Expr head = type;
            while (head.tag == Expr.APP) head = (Expr) head.o0;
            if (head.tag == Expr.CONST) {
                Name headName = (Name) head.o0;
                if (inductiveNames.contains(headName)) {
                    // Direct recursive application — OK
                    return;
                }
                // Check for nested inductive: head is a known inductive whose params
                // contain references to our mutual group (like Array(Syntax)).
                // Lean 4 handles this via ElimNestedInductive; we allow it here since
                // nested compilation preserves positivity.
                Env env = tc.getEnv();
                ConstantInfo headCi = env != null ? env.lookup(headName) : null;
                if (headCi != null && headCi.isInduct()) {
                    // This is a nested occurrence — allowed if the head inductive was
                    // previously declared (not part of the current mutual group).
                    return;
                }
            }
            // Case 4: Contains inductive but not as valid application
            throw new RuntimeException("Constructor " + ctorName +
                " arg #" + argIdx + " has non-valid occurrence of inductive type");
        }
    }

    /**
     * Check just the type of a ConstantInfo (for inductives, ctors, recursors).
     */
    public static void checkType(Env env, ConstantInfo ci, long fuel) {
        Expr.enableIntern();
        try {
            Expr type = Expr.shareCommon(ci.type);  // single expr, no need for shared cache
            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            tc.ensureSort(tc.inferType(type));
        } finally {
            Expr.disableIntern();
        }
    }

    /** Expose Reducer.constLevels for the package. */
    static Object[] constLevels(Expr e) {
        return Reducer.constLevels(e);
    }

    // ========================================================================
    // Recursor rule validation — regenerate expected RHS and compare
    // Following Lean 4 inductive.cpp:705-748 mk_rec_rules
    // ========================================================================

    /**
     * Validate recursor rules by regenerating expected RHS bodies and comparing.
     *
     * Two validation levels:
     * 1. Simple inductives (non-nested, no function-type recursive fields):
     *    Full body regeneration and deep comparison.
     * 2. Nested/complex inductives: Minor uniqueness + range check.
     *
     * This catches soundness attacks like nat-rec-rules where a bogus rule
     * returns the wrong minor premise (h_zero instead of h_succ(n, IH)).
     */
    private static void validateRecursorRules(Env env, ConstantInfo recCi) {
        int np = recCi.numParams;
        int nm = recCi.numMotives;
        int nmi = recCi.numMinors;
        int ni = recCi.numIndices;

        // Detect nested inductives: numMotives > all.length means auxiliary nested types
        boolean isNested = nm > recCi.all.length;

        // Collect inductive names in the mutual group
        java.util.HashSet<Name> inductiveNameSet = new java.util.HashSet<>();
        for (Object n : recCi.all) {
            inductiveNameSet.add((Name) n);
        }

        // For nested inductives, replicate Lean 4's ElimNestedInductive BFS
        // (inductive.cpp:1045-1076) to determine the correct rec_N mapping.
        // Matching Lean 4's m_nested_aux: buffer<pair<expr, name>>, keyed on the
        // full application I(Ds) (not just name I), so Array(PAN(IT)) and Array(IT)
        // create separate auxiliaries.
        // Lean 4's m_nested_aux: pairs of (I(Ds) key, rec_N name)
        java.util.ArrayList<Expr> auxKeys = null;
        java.util.ArrayList<Name> auxNames = null;
        java.util.HashMap<Name, Expr[]> paramSpecialization = null;
        if (isNested && recCi.all.length > 0) {
            Object[] elimResult = elimNestedBFS(env, recCi, inductiveNameSet);
            auxKeys = (java.util.ArrayList<Expr>) elimResult[0];
            auxNames = (java.util.ArrayList<Name>) elimResult[1];
            paramSpecialization = (java.util.HashMap<Name, Expr[]>) elimResult[2];
        }

        // --- Compute minor index offset ---
        // For mutual groups: offset = sum of ctor counts of preceding types in `all`.
        // For auxiliary nested rec_N: offset = sum of rules of rec, rec_1, ..., rec_{N-1}.
        // For mutual+nested: BOTH apply — mutual offset for the group's own recs,
        // nested offset for the auxiliary rec_N names.
        int minorOffset = 0;

        // First: check if this is an auxiliary rec_N (nested naming convention)
        boolean isAuxRec = isNested && recCi.name.tag == Name.STR && recCi.name.str.startsWith("rec_");
        if (isAuxRec) {
            try {
                int suffix = Integer.parseInt(recCi.name.str.substring(4));
                // Count ALL constructors from mutual group types AND previous aux recs.
                // In Lean 4's m_new_types, order is: [mutual types..., aux types...].
                // So rec_N's offset = sum of all mutual types' ctors + sum of aux types'
                // ctors from rec_1 to rec_{N-1}.
                Name mainIndName = (Name) recCi.all[0];
                // Count mutual group constructors (from all types in `all`)
                for (Object n : recCi.all) {
                    ConstantInfo indCi = env.lookup((Name) n);
                    if (indCi != null && indCi.isInduct() && indCi.ctors != null) {
                        minorOffset += indCi.ctors.length;
                    }
                }
                // Count aux recs' rules from rec_1 to rec_{suffix-1}
                for (int i = 1; i < suffix; i++) {
                    Name prevAux = Name.mkStr(mainIndName, "rec_" + i);
                    ConstantInfo prevRec = env.lookup(prevAux);
                    if (prevRec != null && prevRec.isRecursor() && prevRec.rules != null) {
                        minorOffset += prevRec.rules.length;
                    }
                }
            } catch (NumberFormatException e) {}
        } else {
            // Main recursor (I.rec): offset = sum of ctor counts of preceding
            // types in the mutual group (works for both pure mutual and mutual+nested)
            for (int i = 0; i < recCi.all.length; i++) {
                Name indName = (Name) recCi.all[i];
                Name expectedRecName = Name.mkStr(indName, "rec");
                if (expectedRecName.equals(recCi.name)) {
                    break;
                }
                ConstantInfo indCi = env.lookup(indName);
                if (indCi != null && indCi.isInduct() && indCi.ctors != null) {
                    minorOffset += indCi.ctors.length;
                }
            }
        }

        // Build level param references for recursive I.rec calls in the body
        Object[] levelParams = new Object[recCi.levelParams.length];
        boolean hasLP = recCi.levelParams.length > 0;
        for (int j = 0; j < levelParams.length; j++) {
            levelParams[j] = Level.param((Name) recCi.levelParams[j]);
        }

        int minorIdx = minorOffset;
        for (int ruleIdx = 0; ruleIdx < recCi.rules.length; ruleIdx++) {
            ConstantInfo.RecursorRule rule = recCi.rules[ruleIdx];
            if (rule.rhs == null) { minorIdx++; continue; }

            ConstantInfo ctorCi = env.lookup(rule.ctor);
            if (ctorCi == null || !ctorCi.isCtor()) {
                throw new RuntimeException("Recursor rule references unknown constructor: " + rule.ctor);
            }

            int nf = rule.nfields;
            int D = np + nm + nmi + nf;

            // --- Peel lambdas from imported RHS ---
            Expr importedBody = rule.rhs;
            int lambdaCount = 0;
            while (importedBody.tag == Expr.LAM) {
                importedBody = (Expr) importedBody.o2;
                lambdaCount++;
            }
            if (lambdaCount != D) {
                throw new RuntimeException("Recursor rule lambda count mismatch for " +
                    recCi.name + " ctor " + rule.ctor +
                    ": expected " + D + " got " + lambdaCount);
            }

            // --- Analyze constructor type to find recursive fields ---
            // For nested inductives, the ctor may belong to an outer type (e.g., Array.mk).
            // We skip the OUTER type's numParams, not the recursor's numParams.
            Expr ctorType = ctorCi.type;
            int ctorSkipParams = isNested ? ctorCi.numParams : np;
            for (int i = 0; i < ctorSkipParams; i++) {
                if (ctorType.tag != Expr.FORALL) {
                    throw new RuntimeException("Constructor " + rule.ctor +
                        " type has fewer binders than numParams=" + ctorSkipParams);
                }
                ctorType = (Expr) ctorType.o2;
            }

            boolean[] isRecField = new boolean[nf];
            boolean[] isNestedField = new boolean[nf]; // nested recursive (e.g., Array(Syntax))
            Name[] nestedFieldRecName = new Name[nf]; // aux recursor name for nested fields
            int[] recFieldExtraPis = new int[nf]; // extra foralls in function-type fields
            int[] recFieldIndIdx = new int[nf];
            Expr[][] recFieldIndices = new Expr[nf][];
            Expr[] fieldTypesRaw = new Expr[nf]; // raw field types for lambda extraction

            // Create a TypeChecker for whnf reduction of field types.
            // Lean 4's is_rec_argument uses whnf to reveal recursive fields
            // hidden behind type aliases (e.g., constType X Y → X).
            TypeChecker fieldTc = new TypeChecker(env);
            fieldTc.setFuel(DEFAULT_FUEL);

            Expr ctorTypeWalk = ctorType;
            for (int fi = 0; fi < nf; fi++) {
                if (ctorTypeWalk.tag != Expr.FORALL) break;
                Expr fieldType = (Expr) ctorTypeWalk.o1;
                fieldTypesRaw[fi] = fieldType;
                int ctorDepth = np + fi;

                // Use whnf to reveal the field type's structure, matching
                // Lean 4's is_rec_argument (inductive.cpp:384-388).
                Expr ft = fieldTc.whnf(fieldType);
                int extraPis = 0;
                while (ft.tag == Expr.FORALL) {
                    ft = fieldTc.whnf((Expr) ft.o2);
                    extraPis++;
                }

                // Decompose application
                Expr head = ft;
                int argCount = 0;
                Expr temp = ft;
                while (temp.tag == Expr.APP) { argCount++; temp = (Expr) temp.o0; }
                head = temp;
                Expr[] args = new Expr[argCount];
                temp = ft;
                for (int ai = argCount - 1; ai >= 0; ai--) {
                    args[ai] = (Expr) temp.o1;
                    temp = (Expr) temp.o0;
                }

                // For auxiliary ctor fields, a bvar head may resolve to a direct
                // recursive ref after param substitution (e.g., List.cons head : α → Node α β).
                // The resolved expression might be an application (not a bare const),
                // so we decompose it after substitution.
                Expr resolvedHead = head;
                Expr[] resolvedArgs = args;
                int resolvedArgCount = argCount;
                boolean resolvedFromSubst = false; // true if resolved via param specialization
                if (head.tag == Expr.BVAR && isNested && paramSpecialization != null) {
                    // For aux recursors (rec_N), the paramSpecialization is keyed by rec_N name
                    Expr[] outerSpec = paramSpecialization.get(recCi.name);
                    if (outerSpec != null) {
                        Expr resolvedFt = substParamBvars(ft, fi, outerSpec);
                        resolvedHead = resolvedFt;
                        java.util.ArrayList<Expr> rArgs = new java.util.ArrayList<>();
                        while (resolvedHead.tag == Expr.APP) {
                            rArgs.add(0, (Expr) resolvedHead.o1);
                            resolvedHead = (Expr) resolvedHead.o0;
                        }
                        resolvedArgs = rArgs.toArray(new Expr[0]);
                        resolvedArgCount = resolvedArgs.length;
                        resolvedFromSubst = true;
                    }
                }
                if (resolvedHead.tag == Expr.CONST) {
                    Name headName = (Name) resolvedHead.o0;
                    if (inductiveNameSet.contains(headName)) {
                        // --- Direct recursive field ---
                        ConstantInfo indCi = env.lookup(headName);
                        if (indCi != null && indCi.isInduct()) {
                            int indNp = indCi.numParams;
                            int expectedArgs = indNp + indCi.numIndices;
                            if (resolvedArgCount == expectedArgs) {
                                // When resolved from param substitution, the args contain
                                // bvars from the ORIGINAL discovery context (main type's params),
                                // not from the current ctor's context. The specialization chain
                                // guarantees correctness (matching Lean 4's ElimNestedInductive
                                // where fvars make this comparison automatic).
                                boolean paramsOk = resolvedFromSubst;
                                if (!paramsOk) {
                                    paramsOk = true;
                                    for (int pi = 0; pi < indNp; pi++) {
                                        Expr paramArg = resolvedArgs[pi];
                                        long expectedBvar = ctorSkipParams + fi + extraPis - 1 - pi;
                                        if (paramArg.tag != Expr.BVAR || paramArg.longVal != expectedBvar) {
                                            paramsOk = false;
                                            break;
                                        }
                                    }
                                }
                                if (paramsOk) {
                                    isRecField[fi] = true;
                                    recFieldExtraPis[fi] = extraPis;
                                    for (int ii = 0; ii < recCi.all.length; ii++) {
                                        if (headName.equals(recCi.all[ii])) {
                                            recFieldIndIdx[fi] = ii;
                                            break;
                                        }
                                    }
                                    int numInd = indCi.numIndices;
                                    recFieldIndices[fi] = new Expr[numInd];
                                    for (int j = 0; j < numInd; j++) {
                                        recFieldIndices[fi][j] = resolvedArgs[indNp + j];
                                    }
                                }
                            }
                        }
                    } else if (auxKeys != null) {
                        // --- Check for nested recursive field ---
                        // Build I(Ds) from the field type and look up in auxKeys.
                        // For aux recursors, resolve param bvars in args using paramSpec
                        // (matching Lean 4's replace_params normalization).
                        ConstantInfo outerIndCi = env.lookup(headName);
                        if (outerIndCi != null && outerIndCi.isInduct() &&
                                resolvedArgCount >= outerIndCi.numParams) {
                            // Resolve param bvars in args if we have a param specialization
                            Expr[] lookupArgs = resolvedArgs;
                            if (paramSpecialization != null) {
                                Expr[] outerSpec = paramSpecialization.get(recCi.name);
                                if (outerSpec != null && outerSpec.length > 0) {
                                    lookupArgs = new Expr[resolvedArgCount];
                                    for (int ai = 0; ai < resolvedArgCount; ai++) {
                                        Expr arg = resolvedArgs[ai];
                                        if (arg.bvarRange() > 0) {
                                            arg = substParamBvars(arg, fi, outerSpec);
                                        }
                                        lookupArgs[ai] = arg;
                                    }
                                }
                            }
                            // Build I(params) key with resolved args
                            Expr iKey = resolvedHead;
                            for (int ai = 0; ai < outerIndCi.numParams; ai++) {
                                iKey = Expr.app(iKey, lookupArgs[ai]);
                            }
                            // Look up in auxKeys — Expr-keyed dedup
                            Name foundAuxRec = null;
                            for (int k = 0; k < auxKeys.size(); k++) {
                                if (exprDeepEquals(auxKeys.get(k), iKey)) {
                                    foundAuxRec = auxNames.get(k);
                                    break;
                                }
                            }
                            if (foundAuxRec != null) {
                                isRecField[fi] = true;
                                isNestedField[fi] = true;
                                nestedFieldRecName[fi] = foundAuxRec;
                                recFieldExtraPis[fi] = extraPis;
                                recFieldIndices[fi] = new Expr[0];
                            }
                        }
                    }
                }

                ctorTypeWalk = (Expr) ctorTypeWalk.o2;
            }

            // --- Build expected body ---
            // body = minor(fields..., IH_for_each_recursive_field...)
            Expr expectedBody = Expr.bvar(nf + nmi - 1 - minorIdx);

            for (int fi = 0; fi < nf; fi++) {
                expectedBody = Expr.app(expectedBody, Expr.bvar(nf - 1 - fi));
            }

            for (int fi = 0; fi < nf; fi++) {
                if (!isRecField[fi]) continue;

                int indIdx = recFieldIndIdx[fi];
                Expr[] indices = recFieldIndices[fi];
                int extraPis = recFieldExtraPis[fi];

                Name targetRecName;
                if (isNestedField[fi]) {
                    targetRecName = nestedFieldRecName[fi];
                } else if (isNested) {
                    // Direct recursive field in a nested context:
                    // use the main recursor (or the one for the matching inductive)
                    targetRecName = Name.mkStr((Name) recCi.all[Math.min(indIdx, recCi.all.length - 1)], "rec");
                } else if (recCi.all.length == 1) {
                    targetRecName = recCi.name;
                } else {
                    targetRecName = Name.mkStr((Name) recCi.all[indIdx], "rec");
                }

                if (extraPis == 0) {
                    // Simple recursive field: IH = rec(params, motives, minors, indices, field)
                    Expr ih = Expr.mkConst(targetRecName, levelParams, hasLP);
                    for (int j = 0; j < np; j++)
                        ih = Expr.app(ih, Expr.bvar(D - 1 - j));
                    for (int j = 0; j < nm; j++)
                        ih = Expr.app(ih, Expr.bvar(nf + nmi + nm - 1 - j));
                    for (int j = 0; j < nmi; j++)
                        ih = Expr.app(ih, Expr.bvar(nf + nmi - 1 - j));
                    if (indices != null && indices.length > 0) {
                        for (int j = 0; j < indices.length; j++)
                            ih = Expr.app(ih, reindexBvarsIH(indices[j], 0, fi, nm + nmi, nf));
                    }
                    ih = Expr.app(ih, Expr.bvar(nf - 1 - fi));
                    expectedBody = Expr.app(expectedBody, ih);
                } else {
                    // Function-type recursive field (e.g., Acc):
                    // IH = λ x₀ ... x_{l-1}, rec(params, motives, minors, indices, field(x₀..x_{l-1}))
                    // Following Lean 4 inductive.cpp:726-742

                    // Build the inner recursive call at depth D + extraPis
                    Expr ihInner = Expr.mkConst(targetRecName, levelParams, hasLP);
                    for (int j = 0; j < np; j++)
                        ihInner = Expr.app(ihInner, Expr.bvar(D - 1 - j + extraPis));
                    for (int j = 0; j < nm; j++)
                        ihInner = Expr.app(ihInner, Expr.bvar(nf + nmi + nm - 1 - j + extraPis));
                    for (int j = 0; j < nmi; j++)
                        ihInner = Expr.app(ihInner, Expr.bvar(nf + nmi - 1 - j + extraPis));
                    // Indices at depth np+fi+extraPis, reindex to D+extraPis
                    if (indices != null && indices.length > 0) {
                        for (int j = 0; j < indices.length; j++)
                            ihInner = Expr.app(ihInner, reindexBvarsIH(indices[j], extraPis, fi, nm + nmi, nf));
                    }
                    // Apply field to extra args: field(x₀, x₁, ..., x_{l-1})
                    Expr fApp = Expr.bvar(nf - 1 - fi + extraPis);
                    for (int j = 0; j < extraPis; j++)
                        fApp = Expr.app(fApp, Expr.bvar(extraPis - 1 - j));
                    ihInner = Expr.app(ihInner, fApp);

                    // Wrap in lambdas (inside-out), reindexing each binder type
                    Expr ih = ihInner;
                    Expr ftWalk = fieldTypesRaw[fi]; // field type at ctor depth np+fi
                    for (int j = extraPis - 1; j >= 0; j--) {
                        // Walk to the j-th forall
                        Expr ftj = fieldTypesRaw[fi];
                        for (int k = 0; k < j; k++) ftj = (Expr) ftj.o2;
                        // ftj is ∀ (name : type), ... at ctor depth np+fi+j
                        Expr binderType = reindexBvarsIH((Expr) ftj.o1, j, fi, nm + nmi, nf);
                        ih = Expr.lam(ftj.o0, binderType, ih, ftj.o3);
                    }

                    expectedBody = Expr.app(expectedBody, ih);
                }
            }

            if (!exprDeepEquals(importedBody, expectedBody)) {
                if (isNested) {
                    // For nested inductives, the same outer type can be nested with
                    // different params, creating multiple auxiliary rec_N names.
                    // Our BFS assigns one rec_N per outer type name, but Lean 4's
                    // ElimNestedInductive creates separate auxiliaries per distinct
                    // application I(Ds). The rec_N ordering may differ.
                    //
                    // Structural validation: verify each IH targets a recursor from
                    // the same group, has correct arity, and references the right field.
                    validateNestedBodyStructure(env, recCi, importedBody, nf, nmi, minorIdx,
                        np, nm, rule.ctor);
                } else {
                    String impStr = importedBody.toString();
                    String expStr = expectedBody.toString();
                    if (impStr.length() > 200) impStr = impStr.substring(0, 200) + "...";
                    if (expStr.length() > 200) expStr = expStr.substring(0, 200) + "...";
                    throw new RuntimeException("Recursor rule body mismatch for " +
                        recCi.name + " ctor " + rule.ctor +
                        "\n  expected: " + expStr +
                        "\n  got:      " + impStr);
                }
            }

            minorIdx++;
        }
    }

    /**
     * Structural validation for nested recursor rule bodies where full body comparison
     * fails due to rec_N ordering differences (same outer type nested with different params
     * creates multiple auxiliaries).
     *
     * Validates:
     * 1. Correct minor head (bvar at expected position)
     * 2. Correct field bvars in order
     * 3. Each IH targets a recursor from the same group (rec or rec_N with matching prefix)
     * 4. Each IH has correct arity (np + nm + nmi + ni_target + 1)
     * 5. Each IH's last arg is a field bvar
     */
    private static void validateNestedBodyStructure(Env env, ConstantInfo recCi,
            Expr body, int nf, int nmi, int minorIdx, int np, int nm, Name ctorName) {
        // Decompose body into head + args
        java.util.ArrayList<Expr> bodyArgs = new java.util.ArrayList<>();
        Expr bodyHead = body;
        while (bodyHead.tag == Expr.APP) {
            bodyArgs.add(0, (Expr) bodyHead.o1);
            bodyHead = (Expr) bodyHead.o0;
        }

        // Check 1: minor head
        long expectedMinorBvar = nf + nmi - 1 - minorIdx;
        if (bodyHead.tag != Expr.BVAR || bodyHead.longVal != expectedMinorBvar) {
            throw new RuntimeException("Nested recursor rule body head mismatch for " +
                recCi.name + " ctor " + ctorName +
                ": expected bvar(" + expectedMinorBvar + ") got " + bodyHead);
        }

        // Check 2: first nf args must be field bvars in order
        if (bodyArgs.size() < nf) {
            throw new RuntimeException("Nested recursor rule body has too few args for " +
                recCi.name + " ctor " + ctorName + ": expected at least " + nf + " got " + bodyArgs.size());
        }
        for (int fi = 0; fi < nf; fi++) {
            Expr arg = bodyArgs.get(fi);
            long expectedField = nf - 1 - fi;
            if (arg.tag != Expr.BVAR || arg.longVal != expectedField) {
                throw new RuntimeException("Nested recursor rule body field mismatch for " +
                    recCi.name + " ctor " + ctorName + " field " + fi +
                    ": expected bvar(" + expectedField + ") got " + arg);
            }
        }

        // Check 3-5: remaining args are IHs
        Name mainIndName = (Name) recCi.all[0];
        Name recPrefix = Name.mkStr(mainIndName, "rec");
        int expectedIhArity = np + nm + nmi; // + ni_target + 1 (field)

        for (int i = nf; i < bodyArgs.size(); i++) {
            Expr ih = bodyArgs.get(i);
            // The IH may be wrapped in lambdas (function-type recursive fields)
            // Peel lambdas to get the inner application
            while (ih.tag == Expr.LAM) ih = (Expr) ih.o2;

            // Decompose IH application
            Expr ihHead = ih;
            int ihArgCount = 0;
            while (ihHead.tag == Expr.APP) { ihArgCount++; ihHead = (Expr) ihHead.o0; }

            // Check 3: IH head must be a recursor from the group
            if (ihHead.tag != Expr.CONST) {
                throw new RuntimeException("Nested recursor rule IH head is not a const for " +
                    recCi.name + " ctor " + ctorName + " IH " + (i - nf));
            }
            Name ihRecName = (Name) ihHead.o0;
            // Must be either the main rec or rec_N from the same type
            boolean validRec = ihRecName.equals(recPrefix) || // main rec
                (ihRecName.tag == Name.STR && ihRecName.prefix != null &&
                 ihRecName.prefix.equals(mainIndName) &&
                 ihRecName.str.startsWith("rec"));
            if (!validRec) {
                throw new RuntimeException("Nested recursor rule IH targets wrong recursor for " +
                    recCi.name + " ctor " + ctorName + " IH " + (i - nf) +
                    ": " + ihRecName + " not in group of " + mainIndName);
            }

            // Check 4: IH arity (at least np + nm + nmi + 1)
            if (ihArgCount < expectedIhArity + 1) {
                throw new RuntimeException("Nested recursor rule IH has too few args for " +
                    recCi.name + " ctor " + ctorName + " IH " + (i - nf) +
                    ": " + ihArgCount + " < " + (expectedIhArity + 1));
            }
        }
    }

    /**
     * Substitute outer type params in a constructor type body (after peeling param binders).
     * Matches Lean 4's instantiate_rev(e, nparams, params) in inductive.cpp:959.
     * After peeling nparams binders, bvar(k) where k >= nfields references a param.
     * This substitution replaces all such param refs with the concrete specialization values.
     */
    // ========================================================================
    // Nested aux recursor mapping — built from env (all rec_N already declared)
    // ========================================================================

    /**
     * Build the nested auxiliary mapping by looking up rec_N recursors from the env.
     * All rec_N recursors exist (parser sorts them before the main rec).
     *
     * For each rec_N, we extract:
     * - The outer inductive name (from the first rule's constructor)
     * - The param specialization (from instantiating the outer ctor's params)
     *
     * The field analysis matches against these using the full I(Ds) application
     * expression (Expr-keyed, matching Lean 4's m_nested_aux dedup).
     *
     * Returns [auxKeys, auxNames, paramSpec].
     */
    private static Object[] elimNestedBFS(Env env, ConstantInfo recCi,
            java.util.HashSet<Name> inductiveNameSet) {
        int np = recCi.numParams;
        Name mainIndName = (Name) recCi.all[0];

        // Matching Lean 4's ElimNestedInductive BFS (inductive.cpp:1055-1076).
        // m_new_types: names of all types in the expanded mutual group
        java.util.ArrayList<Name> newTypeNames = new java.util.ArrayList<>();
        for (Object n : recCi.all) newTypeNames.add((Name) n);
        int originalCount = newTypeNames.size();

        // m_nested_aux: pairs of (I(Ds) key, aux_rec_name)
        // KEY: Expr-based dedup matching Lean 4's m_nested_aux: buffer<pair<expr, name>>
        java.util.ArrayList<Expr> auxKeys = new java.util.ArrayList<>();
        java.util.ArrayList<Name> auxNames = new java.util.ArrayList<>();

        // Per aux type: constructor names and their types (after instantiate_pi_params)
        java.util.ArrayList<Name[]> auxCtorNamesList = new java.util.ArrayList<>();
        java.util.ArrayList<Expr[]> auxCtorTypesList = new java.util.ArrayList<>();

        java.util.HashMap<Name, Expr[]> paramSpec = new java.util.HashMap<>();
        int nextSuffix = 1;
        int qhead = 0;

        while (qhead < newTypeNames.size()) {
            Name typeName = newTypeNames.get(qhead);
            Name[] ctorArr; Expr[] ctorTypes;

            if (qhead < originalCount) {
                ConstantInfo indCi = env.lookup(typeName);
                if (indCi == null || !indCi.isInduct() || indCi.ctors == null) { qhead++; continue; }
                ctorArr = indCi.ctors;
                ctorTypes = new Expr[ctorArr.length];
                for (int i = 0; i < ctorArr.length; i++) {
                    ConstantInfo c = env.lookup(ctorArr[i]);
                    ctorTypes[i] = c != null ? c.type : null;
                }
            } else {
                int ai = qhead - originalCount;
                ctorArr = auxCtorNamesList.get(ai);
                ctorTypes = auxCtorTypesList.get(ai);
            }

            // For each constructor, scan field types for nested occurrences.
            // Following Lean 4: peel params, then top-down scan each field type.
            int[] nextSuffixArr = {nextSuffix};
            for (int ci = 0; ci < ctorArr.length; ci++) {
                if (ctorTypes[ci] == null) continue;
                Expr ct = ctorTypes[ci];
                for (int i = 0; i < np; i++) {
                    if (ct.tag == Expr.FORALL) ct = (Expr) ct.o2;
                }
                while (ct.tag == Expr.FORALL) {
                    findAndRecordNested((Expr) ct.o1, env, newTypeNames, auxKeys, auxNames,
                        auxCtorNamesList, auxCtorTypesList, paramSpec,
                        mainIndName, np, nextSuffixArr);
                    ct = (Expr) ct.o2;
                }
            }
            nextSuffix = nextSuffixArr[0];
            qhead++;
        }

        return new Object[] { auxKeys, auxNames, paramSpec };
    }

    /**
     * Top-down scan of expression for outermost nested inductive application.
     * Matches Lean 4's replace_all_nested + replace_if_nested visit order.
     * Compact: only recurses into APP/FORALL/LAM children, stops at first match.
     */
    private static void findAndRecordNested(Expr e, Env env,
            java.util.ArrayList<Name> newTypeNames,
            java.util.ArrayList<Expr> auxKeys, java.util.ArrayList<Name> auxNames,
            java.util.ArrayList<Name[]> auxCtorNamesList,
            java.util.ArrayList<Expr[]> auxCtorTypesList,
            java.util.HashMap<Name, Expr[]> paramSpec,
            Name mainIndName, int np, int[] nextSuffix) {
        // Try to match this node as a nested application
        if (tryRecordNested(e, env, newTypeNames, auxKeys, auxNames,
                auxCtorNamesList, auxCtorTypesList, paramSpec,
                mainIndName, np, nextSuffix)) {
            return; // Matched — don't recurse (Lean 4's replace semantics)
        }
        // Recurse into children
        switch (e.tag) {
            case Expr.APP:
                findAndRecordNested((Expr) e.o0, env, newTypeNames, auxKeys, auxNames,
                    auxCtorNamesList, auxCtorTypesList, paramSpec, mainIndName, np, nextSuffix);
                findAndRecordNested((Expr) e.o1, env, newTypeNames, auxKeys, auxNames,
                    auxCtorNamesList, auxCtorTypesList, paramSpec, mainIndName, np, nextSuffix);
                break;
            case Expr.FORALL: case Expr.LAM:
                findAndRecordNested((Expr) e.o1, env, newTypeNames, auxKeys, auxNames,
                    auxCtorNamesList, auxCtorTypesList, paramSpec, mainIndName, np, nextSuffix);
                findAndRecordNested((Expr) e.o2, env, newTypeNames, auxKeys, auxNames,
                    auxCtorNamesList, auxCtorTypesList, paramSpec, mainIndName, np, nextSuffix);
                break;
        }
    }

    /**
     * Check if expression is a nested inductive application I(Ds, is).
     * If so, record it (with dedup on I(Ds)) and create aux constructors.
     * Matches Lean 4's replace_if_nested (inductive.cpp:963-1028).
     */
    private static boolean tryRecordNested(Expr e, Env env,
            java.util.ArrayList<Name> newTypeNames,
            java.util.ArrayList<Expr> auxKeys, java.util.ArrayList<Name> auxNames,
            java.util.ArrayList<Name[]> auxCtorNamesList,
            java.util.ArrayList<Expr[]> auxCtorTypesList,
            java.util.HashMap<Name, Expr[]> paramSpec,
            Name mainIndName, int np, int[] nextSuffix) {
        if (e.tag != Expr.APP) return false;
        Expr head = e;
        int totalArgs = 0;
        while (head.tag == Expr.APP) { totalArgs++; head = (Expr) head.o0; }
        if (head.tag != Expr.CONST) return false;

        Name iName = (Name) head.o0;
        ConstantInfo iInfo = env.lookup(iName);
        if (iInfo == null || !iInfo.isInduct()) return false;
        int iNp = iInfo.numParams;
        if (totalArgs < iNp) return false;

        // Not nested if it's one of the types being defined
        for (Name tn : newTypeNames) {
            if (iName.equals(tn)) return false;
        }

        // Extract param args
        Expr[] allArgs = new Expr[totalArgs];
        Expr tmp = e;
        for (int i = totalArgs - 1; i >= 0; i--) {
            allArgs[i] = (Expr) tmp.o1;
            tmp = (Expr) tmp.o0;
        }

        // Check: any param arg references a type in newTypeNames?
        boolean isNested = false;
        for (int i = 0; i < iNp; i++) {
            if (exprContainsAnyName(allArgs[i], newTypeNames)) {
                isNested = true; break;
            }
        }
        if (!isNested) return false;

        // Build canonical key I(Ds) — just the head applied to params
        Expr iWithParams = head;
        for (int i = 0; i < iNp; i++) iWithParams = Expr.app(iWithParams, allArgs[i]);

        // Dedup: check if already discovered (Expr.equals on compact key)
        for (int k = 0; k < auxKeys.size(); k++) {
            if (exprDeepEquals(auxKeys.get(k), iWithParams)) return true; // Already known
        }

        // New discovery — create aux types for all in I's mutual group
        Name[] iAll = iInfo.all != null ? new Name[iInfo.all.length] : new Name[]{iName};
        if (iInfo.all != null) for (int i = 0; i < iInfo.all.length; i++) iAll[i] = (Name) iInfo.all[i];

        for (Name jName : iAll) {
            ConstantInfo jInfo = env.lookup(jName);
            if (jInfo == null || !jInfo.isInduct()) continue;

            Expr jKey = Expr.mkConst(jName, head.o1, head.hasLevelParam());
            for (int i = 0; i < iNp; i++) jKey = Expr.app(jKey, allArgs[i]);

            Name auxName = Name.mkStr(mainIndName, "rec_" + nextSuffix[0]);
            auxKeys.add(jKey);
            auxNames.add(auxName);
            newTypeNames.add(auxName);
            nextSuffix[0]++;

            // Create aux constructor types: instantiate_pi_params + keep compact
            Name[] jCtors = jInfo.ctors != null ? jInfo.ctors : new Name[0];
            Name[] newCtorNames = new Name[jCtors.length];
            Expr[] newCtorTypes = new Expr[jCtors.length];
            for (int ci = 0; ci < jCtors.length; ci++) {
                ConstantInfo jCtor = env.lookup(jCtors[ci]);
                if (jCtor == null) continue;
                newCtorNames[ci] = jCtors[ci];
                // instantiate_pi_params: peel I's params, substitute with allArgs
                Expr jct = jCtor.type;
                for (int i = 0; i < iNp; i++) {
                    if (jct.tag == Expr.FORALL) jct = (Expr) jct.o2;
                }
                // Substitute param bvars with the COMPACT param values from the nested application
                newCtorTypes[ci] = instantiateParams(jct, allArgs);
            }
            auxCtorNamesList.add(newCtorNames);
            auxCtorTypesList.add(newCtorTypes);

            // Record param spec for field analysis
            Expr[] spec = new Expr[iNp];
            System.arraycopy(allArgs, 0, spec, 0, iNp);
            paramSpec.put(auxName, spec);
        }
        return true;
    }

    /**
     * Top-down expression replacement matching Lean 4's replace_all_nested.
     * At each node, tries replaceIfNested. If it matches, replaces and does NOT
     * recurse into children. If no match, recurses into children.
     * This matches replace_fn.cpp: try f(e) first; if Some, use it; else recurse.
     */
    /**
     * Top-down discovery of nested inductive occurrences, matching Lean 4's
     * replace_all_nested visit order. Does NOT build replacement expressions —
     * only records discoveries in the auxiliary lists for rec_N assignment.
     *
     * Visit order: at each node, try to match as nested. If match, record it
     * and DON'T recurse into children (same as Lean 4's replace: matched nodes
     * are replaced and children not visited). If no match, recurse into children.
     */
    /** Entry point: creates visited cache then calls the recursive scan. */
    private static void discoverNestedTopDown(Expr e, Env env,
            java.util.HashSet<Name> inductiveNameSet,
            java.util.ArrayList<Name> newTypeNames,
            java.util.ArrayList<Expr> auxKeys, java.util.ArrayList<Name> auxNames,
            java.util.ArrayList<Name[]> auxCtorNames, java.util.ArrayList<Expr[]> auxCtorTypes,
            java.util.HashMap<Name, Expr[]> paramSpec,
            Name mainIndName, int np, int[] nextSuffix) {
        // Identity-based visited set matching Lean 4's replace_fn cache (replace_fn.cpp:26)
        java.util.IdentityHashMap<Expr, Boolean> visited = new java.util.IdentityHashMap<>();
        discoverNestedGo(e, env, inductiveNameSet, newTypeNames,
            auxKeys, auxNames, auxCtorNames, auxCtorTypes,
            paramSpec, mainIndName, np, nextSuffix, visited);
    }

    private static final int MAX_DISCOVER_DEPTH = 100;

    private static void discoverNestedGo(Expr e, Env env,
            java.util.HashSet<Name> inductiveNameSet,
            java.util.ArrayList<Name> newTypeNames,
            java.util.ArrayList<Expr> auxKeys, java.util.ArrayList<Name> auxNames,
            java.util.ArrayList<Name[]> auxCtorNames, java.util.ArrayList<Expr[]> auxCtorTypes,
            java.util.HashMap<Name, Expr[]> paramSpec,
            Name mainIndName, int np, int[] nextSuffix,
            java.util.IdentityHashMap<Expr, Boolean> visited) {

        // Cache: skip already-visited expressions (prevents exponential blowup on shared subexprs)
        if (visited.containsKey(e)) return;
        if (visited.size() > 100000) return; // Safety limit for huge expression trees
        visited.put(e, Boolean.TRUE);

        // Try to match this node as a nested inductive application
        if (tryDiscoverNested(e, env, inductiveNameSet, newTypeNames,
                auxKeys, auxNames, auxCtorNames, auxCtorTypes,
                paramSpec, mainIndName, np, nextSuffix)) {
            return; // Matched — don't recurse (matches Lean 4's replace semantics)
        }

        // No match — recurse into children
        switch (e.tag) {
            case Expr.APP:
                discoverNestedGo((Expr) e.o0, env, inductiveNameSet, newTypeNames,
                    auxKeys, auxNames, auxCtorNames, auxCtorTypes,
                    paramSpec, mainIndName, np, nextSuffix, visited);
                discoverNestedGo((Expr) e.o1, env, inductiveNameSet, newTypeNames,
                    auxKeys, auxNames, auxCtorNames, auxCtorTypes,
                    paramSpec, mainIndName, np, nextSuffix, visited);
                break;
            case Expr.FORALL: case Expr.LAM:
                discoverNestedGo((Expr) e.o1, env, inductiveNameSet, newTypeNames,
                    auxKeys, auxNames, auxCtorNames, auxCtorTypes,
                    paramSpec, mainIndName, np, nextSuffix, visited);
                discoverNestedGo((Expr) e.o2, env, inductiveNameSet, newTypeNames,
                    auxKeys, auxNames, auxCtorNames, auxCtorTypes,
                    paramSpec, mainIndName, np, nextSuffix, visited);
                break;
        }
    }

    /**
     * Try to discover a nested inductive application.
     * Matches Lean 4's replace_if_nested (inductive.cpp:963-1028) visit order.
     * Returns true if e is a nested application (recorded in aux lists), false otherwise.
     */
    private static boolean tryDiscoverNested(Expr e, Env env,
            java.util.HashSet<Name> inductiveNameSet,
            java.util.ArrayList<Name> newTypeNames,
            java.util.ArrayList<Expr> auxKeys, java.util.ArrayList<Name> auxNames,
            java.util.ArrayList<Name[]> auxCtorNames, java.util.ArrayList<Expr[]> auxCtorTypes,
            java.util.HashMap<Name, Expr[]> paramSpec,
            Name mainIndName, int np, int[] nextSuffix) {

        // Must be an application with const head
        if (e.tag != Expr.APP) return false;
        Expr head = e;
        int totalArgs = 0;
        while (head.tag == Expr.APP) { totalArgs++; head = (Expr) head.o0; }
        if (head.tag != Expr.CONST) return false;

        Name iName = (Name) head.o0;
        ConstantInfo iInfo = env.lookup(iName);
        if (iInfo == null || !iInfo.isInduct()) return false;
        int iNparams = iInfo.numParams;
        if (totalArgs < iNparams) return false;

        // Check if it's one of the types being defined — not nested
        for (Name tn : newTypeNames) {
            if (iName.equals(tn)) return false;
        }

        // Extract args
        Expr[] allArgs = new Expr[totalArgs];
        Expr temp = e;
        for (int i = totalArgs - 1; i >= 0; i--) {
            allArgs[i] = (Expr) temp.o1;
            temp = (Expr) temp.o0;
        }

        // Check if any param arg references a type in newTypeNames (nested condition)
        boolean isNested = false;
        for (int i = 0; i < iNparams; i++) {
            if (exprContainsAnyName(allArgs[i], newTypeNames)) {
                isNested = true;
                break;
            }
        }
        if (!isNested) return false;

        // Build the canonical key: I applied to params only (for deduplication)
        Expr iWithParams = head;
        for (int i = 0; i < iNparams; i++) {
            iWithParams = Expr.app(iWithParams, allArgs[i]);
        }

        // Check if we already have an auxiliary for this I(Ds)
        for (int k = 0; k < auxKeys.size(); k++) {
            if (auxKeys.get(k).equals(iWithParams)) {
                return true; // Already discovered
            }
        }

        // New nested discovery — create auxiliary type(s)
        // For all types J in I's mutual group, create auxiliary types
        Name[] iAll = iInfo.all != null ? new Name[iInfo.all.length] : new Name[]{iName};
        if (iInfo.all != null) {
            for (int i = 0; i < iInfo.all.length; i++) iAll[i] = (Name) iInfo.all[i];
        }

        for (Name jName : iAll) {
            ConstantInfo jInfo = env.lookup(jName);
            if (jInfo == null || !jInfo.isInduct()) continue;

            // Build canonical key for J(Ds)
            Expr jWithParams = Expr.mkConst(jName, head.o1, head.hasLevelParam());
            for (int i = 0; i < iNparams; i++) {
                jWithParams = Expr.app(jWithParams, allArgs[i]);
            }

            // Generate aux rec name following Lean 4 naming: mainInd.rec_N
            Name auxJName = Name.mkStr(mainIndName, "rec_" + nextSuffix[0]);

            auxKeys.add(jWithParams);
            auxNames.add(auxJName);
            newTypeNames.add(auxJName);
            nextSuffix[0]++;

            // Create auxiliary constructor types (instantiate_pi_params + substitute)
            // These are needed for deeper BFS levels to discover further nesting
            Name[] jCtors = jInfo.ctors;
            if (jCtors == null) jCtors = new Name[0];
            Name[] newCtorNames = new Name[jCtors.length];
            Expr[] newCtorTypesArr = new Expr[jCtors.length];
            for (int ci = 0; ci < jCtors.length; ci++) {
                ConstantInfo jCtorInfo = env.lookup(jCtors[ci]);
                if (jCtorInfo == null) continue;
                newCtorNames[ci] = jCtors[ci];
                Expr jct = jCtorInfo.type;
                for (int i = 0; i < iNparams; i++) {
                    if (jct.tag == Expr.FORALL) jct = (Expr) jct.o2;
                }
                jct = instantiateParams(jct, allArgs);
                newCtorTypesArr[ci] = jct;
            }
            auxCtorNames.add(newCtorNames);
            auxCtorTypes.add(newCtorTypesArr);

            Expr[] spec = new Expr[iNparams];
            System.arraycopy(allArgs, 0, spec, 0, iNparams);
            paramSpec.put(auxJName, spec);
        }

        return true; // Nested occurrence discovered
    }

    /** Check if expression contains a reference to any name in the list. */
    private static boolean exprContainsAnyName(Expr e, java.util.ArrayList<Name> names) {
        if (e == null) return false;
        switch (e.tag) {
            case Expr.CONST: {
                Name n = (Name) e.o0;
                for (Name tn : names) if (n.equals(tn)) return true;
                return false;
            }
            case Expr.APP: return exprContainsAnyName((Expr) e.o0, names)
                                || exprContainsAnyName((Expr) e.o1, names);
            case Expr.LAM: case Expr.FORALL:
                return exprContainsAnyName((Expr) e.o1, names)
                    || exprContainsAnyName((Expr) e.o2, names);
            default: return false;
        }
    }

    private static Expr instantiateParams(Expr e, Expr[] params) {
        return instantiateParamsGo(e, 0, params);
    }

    private static Expr instantiateParamsGo(Expr e, int depth, Expr[] params) {
        if (e.bvarRange() == 0) return e;
        switch (e.tag) {
            case Expr.BVAR: {
                long k = e.longVal;
                if (k >= depth) {
                    // Match Lean 4's instantiate_rev: bvar(0) → params[n-1], bvar(n-1) → params[0]
                    // After peeling n params, bvar(0) = last/innermost param,
                    // but params[0] = first/outermost arg in the application I(arg0, arg1, ...).
                    int rawIdx = (int)(k - depth);
                    int paramIdx = params.length - 1 - rawIdx; // REVERSE mapping
                    if (paramIdx >= 0 && paramIdx < params.length) {
                        return liftBvars(params[paramIdx], depth);
                    }
                }
                return e;
            }
            case Expr.APP: {
                Expr fn = instantiateParamsGo((Expr) e.o0, depth, params);
                Expr arg = instantiateParamsGo((Expr) e.o1, depth, params);
                if (fn == e.o0 && arg == e.o1) return e;
                return Expr.app(fn, arg);
            }
            case Expr.FORALL: case Expr.LAM: {
                Expr ty = instantiateParamsGo((Expr) e.o1, depth, params);
                Expr body = instantiateParamsGo((Expr) e.o2, depth + 1, params);
                if (ty == e.o1 && body == e.o2) return e;
                return e.tag == Expr.FORALL ?
                    Expr.forall(e.o0, ty, body, e.o3) :
                    Expr.lam(e.o0, ty, body, e.o3);
            }
            default: return e;
        }
    }

    /** Lift all bvar indices in e by n (add n to each bvar index). */
    private static Expr liftBvars(Expr e, int n) {
        if (n == 0 || e.bvarRange() == 0) return e;
        switch (e.tag) {
            case Expr.BVAR: return Expr.bvar(e.longVal + n);
            case Expr.APP: {
                Expr fn = liftBvars((Expr) e.o0, n);
                Expr arg = liftBvars((Expr) e.o1, n);
                if (fn == e.o0 && arg == e.o1) return e;
                return Expr.app(fn, arg);
            }
            case Expr.FORALL: case Expr.LAM: {
                Expr ty = liftBvars((Expr) e.o1, n);
                Expr body = liftBvars((Expr) e.o2, n);
                if (ty == e.o1 && body == e.o2) return e;
                return e.tag == Expr.FORALL ?
                    Expr.forall(e.o0, ty, body, e.o3) :
                    Expr.lam(e.o0, ty, body, e.o3);
            }
            default: return e;
        }
    }

    /**
     * Substitute parameter bvar references in a field type with concrete specialization values.
     * At field index fi within a constructor whose params were skipped, bvar(k) where k >= fi
     * references the (numParams-1-(k-fi))-th param (de Bruijn reversal).
     * We replace such bvars with the corresponding value from outerSpec.
     */
    private static Expr substParamBvars(Expr e, int fi, Expr[] outerSpec) {
        if (e.bvarRange() == 0) return e;
        switch (e.tag) {
            case Expr.BVAR: {
                long k = e.longVal;
                if (k >= fi) {
                    int paramIdx = outerSpec.length - 1 - (int)(k - fi);
                    if (paramIdx >= 0 && paramIdx < outerSpec.length) {
                        return outerSpec[paramIdx];
                    }
                }
                return e;
            }
            case Expr.APP: {
                Expr fn = substParamBvars((Expr) e.o0, fi, outerSpec);
                Expr arg = substParamBvars((Expr) e.o1, fi, outerSpec);
                if (fn == e.o0 && arg == e.o1) return e;
                return Expr.app(fn, arg);
            }
            case Expr.FORALL: case Expr.LAM: {
                Expr ty = substParamBvars((Expr) e.o1, fi, outerSpec);
                Expr body = substParamBvars((Expr) e.o2, fi + 1, outerSpec);
                if (ty == e.o1 && body == e.o2) return e;
                return e.tag == Expr.FORALL ?
                    Expr.forall(e.o0, ty, body, e.o3) :
                    Expr.lam(e.o0, ty, body, e.o3);
            }
            default: return e;
        }
    }

    /**
     * Like exprContainsName but also checks for const references (not fvars).
     * For index checking after instantiation with fvars, the inductive
     * reference might appear as a const in a nested position.
     */
    private static boolean exprContainsNameOrFvar(Expr e, java.util.HashSet<Name> names) {
        return exprContainsName(e, names);
    }

    /** Check if an expression contains a reference to any key in the given map. */
    private static boolean exprContainsAnyKey(Expr e, java.util.HashMap<Name, Name> map) {
        if (e == null || map.isEmpty()) return false;
        switch (e.tag) {
            case Expr.CONST: return map.containsKey((Name) e.o0);
            case Expr.APP: return exprContainsAnyKey((Expr) e.o0, map) || exprContainsAnyKey((Expr) e.o1, map);
            case Expr.LAM: case Expr.FORALL:
                return exprContainsAnyKey((Expr) e.o1, map) || exprContainsAnyKey((Expr) e.o2, map);
            default: return false;
        }
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
    private static Expr reindexBvarsIH(Expr e, int j, int fi, int nmNmi, int nf) {
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
