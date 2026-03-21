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
    private final IdentityHashMap<Expr, Expr> inferCache;      // for check mode (infer_only=false)
    private final IdentityHashMap<Expr, Expr> inferOnlyCache;  // for infer_only mode (infer_only=true)
    private final IdentityHashMap<Expr, IdentityHashMap<Expr, Boolean>> failureCache;
    // Identity-based cache for isDefEqCore results.
    // Prevents exponential re-comparison of DAG-shared expression pairs.
    // Key: identity of (t,s) pair. Value: Boolean result.
    private final IdentityHashMap<Expr, IdentityHashMap<Expr, Boolean>> isDefEqIdentityCache;
    private long nextId;
    private int isDefEqDepth;
    public boolean tracing;
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
        return this.reducer.getStats();
    }

    /** Get the ring buffer trace from the Reducer. */
    public String[] getReducerTrace() {
        return this.reducer.getTraceRing();
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
     * Full type check — used by checkConstant/checkType (Lean's check()).
     * Matches Lean's infer_type_core(e, false).
     */
    public Expr inferType(Expr e) {
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
                int fieldIdx = (int) e.longVal;
                for (int i = 0; i < fieldIdx && ctorType.tag == Expr.FORALL; i++) {
                    ctorType = Reducer.instantiate1((Expr) ctorType.o2, Expr.proj(e.o0, i, (Expr) e.o1));
                }
                if (ctorType.tag == Expr.FORALL) {
                    result = (Expr) ctorType.o1;
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
        boolean result = isDefEqCore(t, s);
        if (result) {
            eqvManager.addEquiv(t, s);
        }
        return result;
    }

    private static final int ISDEFEQ_CACHE_MAX = 65536;

    private boolean isDefEqCore(Expr t, Expr s) {
        if (t.isEqp(s)) return true;
        reducer.checkFuelPublic();
        // Identity-based cache: avoid re-comparing the same (identity) pair
        // of expressions that arises from DAG sharing.
        IdentityHashMap<Expr, Boolean> innerMap = isDefEqIdentityCache.get(t);
        if (innerMap != null) {
            Boolean cached = innerMap.get(s);
            if (cached != null) return cached;
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
            }
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

        // Step 1: Quick check (Lean 4 line 1061)
        {
            int q = quickIsDefEq(t, s);
            if (q != 0) {
                boolean r = q == 1;
                if (doEmit) emitTrace(lFp, rFp, r, "quick");
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

        // Step 2: whnf_core with Lean 4 flags (cheapRec=false, cheapProj=true)
        Expr tn = reducer.whnfCore(t, false, true);
        Expr sn = reducer.whnfCore(s, false, true);

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
                return true;
            }
            if (piResult == -1) {
                if (doTrace) trace("=> proofIrrel FAIL");
                if (doEmit) emitTrace(lFp, rFp, false, "proof_irrel");
                return false;
            }
        }

        // Step 4: Lazy delta reduction
        int deltaResult = lazyDeltaReduction(tn, sn);
        if (deltaResult == 1) {
            if (doTrace) trace("=> lazyDelta EQ");
            if (doEmit) emitTrace(lFp, rFp, true, "lazy_delta");
            return true;
        }
        if (deltaResult == -1) {
            if (doTrace) trace("=> lazyDelta NEQ");
            if (doEmit) emitTrace(lFp, rFp, false, "lazy_delta");
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
            Expr tn2 = reducer.whnfCore(tn, false, false);
            Expr sn2 = reducer.whnfCore(sn, false, false);
            if (!tn2.isEqp(tn) || !sn2.isEqp(sn)) {
                boolean r = isDefEqCore(tn2, sn2);
                if (doEmit) emitTrace(lFp, rFp, r, "whnfcore2");
                return r;
            }
        }

        // Step 7: Sort comparison
        if (tn.tag == Expr.SORT && sn.tag == Expr.SORT) {
            boolean r = Level.eq((Level) tn.o0, (Level) sn.o0);
            if (doEmit) emitTrace(lFp, rFp, r, "sort_eq");
            return r;
        }

        // Step 8: App congruence
        if (tn.tag == Expr.APP && sn.tag == Expr.APP) {
            if (isDefEqApp(tn, sn)) {
                if (doEmit) emitTrace(lFp, rFp, true, "app");
                return true;
            }
        }

        // Step 9: Lambda/forall congruence
        if ((tn.tag == Expr.LAM && sn.tag == Expr.LAM) ||
            (tn.tag == Expr.FORALL && sn.tag == Expr.FORALL)) {
            boolean r = isDefEqBinding(tn, sn);
            if (doEmit) emitTrace(lFp, rFp, r, "binding");
            return r;
        }

        // Step 10: Eta expansion
        if (tryEta(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta"); return true; }
        if (tryEta(sn, tn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta"); return true; }

        // Step 11: Eta struct expansion
        if (tryEtaStruct(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "eta_struct"); return true; }

        // Step 11b: String literal expansion
        {
            int r = tryStringLitExpansion(tn, sn);
            if (r == 1) { if (doEmit) emitTrace(lFp, rFp, true, "string_lit"); return true; }
            if (r == -1) { if (doEmit) emitTrace(lFp, rFp, false, "string_lit"); return false; }
        }

        // Step 12: Unit-like types
        if (isDefEqUnitLike(tn, sn)) { if (doEmit) emitTrace(lFp, rFp, true, "unit_like"); return true; }

        // Step 13: Proof irrelevance (after full reduction — extra, not in Lean)
        {
            int piResult2 = proofIrrelevant(tn, sn);
            if (piResult2 == 1) {
                if (doTrace) trace("=> proofIrrel(late)");
                if (doEmit) emitTrace(lFp, rFp, true, "proof_irrel2");
                return true;
            }
            if (piResult2 == -1) {
                if (doTrace) trace("=> proofIrrel(late) FAIL");
                if (doEmit) emitTrace(lFp, rFp, false, "proof_irrel2");
                return false;
            }
        }

        if (doTrace) {
            trace("=> FAIL d=" + isDefEqDepth + " " + exprSummary(tn, 4) + " =?= " + exprSummary(sn, 4));
        }
        if (doEmit) emitTrace(lFp, rFp, false, "fail");
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
                    tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
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
                    sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
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
                    tn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) tnFA[1]), false, true);
                } else if (cmp > 0) {
                    // Unfold right
                    Expr unfolded = reducer.tryUnfoldDef(snHead);
                    if (unfolded == null) return 0;
                    sn = reducer.whnfCore(Reducer.mkApps(unfolded, (Expr[]) snFA[1]), false, true);
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
                        tn = reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true);
                    }
                    if (unfoldedS != null) {
                        sn = reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true);
                    }
                }
            }

            // Quick check after update (Lean 4 line 937: quick_is_def_eq)
            deltaHolder[0] = tn;
            deltaHolder[1] = sn;
            {
                int q = quickIsDefEq(tn, sn);
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
            int tHints = getHints(tnHead);
            int sHints = getHints(snHead);
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
                    tn = reducer.whnfCore(Reducer.mkApps(unfoldedT, (Expr[]) tnFA[1]), false, true);
                    holder[0] = tn;
                }
                if (unfoldedS != null) {
                    sn = reducer.whnfCore(Reducer.mkApps(unfoldedS, (Expr[]) snFA[1]), false, true);
                    holder[1] = sn;
                }
            }
        }
        // Quick check after reduction (matching Lean's quick_is_def_eq after step)
        {
            int q = quickIsDefEq(tn, sn);
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
            // Share common sub-expressions before type-checking.
            // Use a shared cache so type and value share identity for common sub-expressions.
            java.util.HashMap<Expr, Expr> scCache = new java.util.HashMap<>(4096);
            java.util.IdentityHashMap<Expr, Expr> scVisited = new java.util.IdentityHashMap<>(4096);
            Expr type = Expr.shareCommon(ci.type, scCache, scVisited);
            Expr value = ci.value != null ? Expr.shareCommon(ci.value, scCache, scVisited) : null;

            TypeChecker tc = new TypeChecker(env);
            tc.setFuel(fuel);
            // Theorem: check is_prop first, matching Lean 4's add_theorem
            if (ci.isThm()) {
                if (!tc.isProp(type))
                    throw new RuntimeException("Type error: Theorem type is not a proposition for " + ci.name);
            }

            // Check type is well-formed (must be a sort)
            tc.ensureSort(tc.inferType(type));

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
            return env.addConstant(ci);
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
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), tc.getReducerTrace(), null};
            } catch (RuntimeException ex) {
                return new Object[]{tc.getFuelUsed(), tc.getReducerStats(), tc.getReducerTrace(), ex.getMessage()};
            }
        } finally {
            Expr.disableIntern();
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
}
