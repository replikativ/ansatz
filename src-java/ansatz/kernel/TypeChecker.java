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
    // Here a local is a numeric id, and callers (AddInductive's LocalCtx, the elaborator)
    // number theirs from small counters. The checker's own locals
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
            sb.append("}\n");
            traceWriter.write(sb.toString());
        } catch (IOException e) {
            // silently ignore write failures
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
        this.reducer.setCallbacks(this::inferTypeOnly, this::isDefEq, this::isProp);
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
     * proj-of-subst-prop, rec-of-subst-prop). The zero test is Lean's normalizes_to_zero, matching
     * Lean's is_zero rather than a syntactic ZERO tag.
     */
    private boolean isProp(Expr e) {
        Expr t = whnf(inferTypeOnly(e));
        if (t.tag != Expr.SORT) {
            throw new RuntimeException("Type error: type expected, got " + t + " (is_prop on a stuck sort — lean4#14807)");
        }
        return Level.normalizesToZero((Level) t.o0);
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
                if (!removeDeadLet || AddInductive.hasLooseBVar(r, 0)) {   // local_ctx::mk_binding: #0 occurs
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
        if (e.bvarRange() > 0)
            throw new RuntimeException("type checker does not support loose bound variables, replace them with free variables before invoking it");
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

            case Expr.PROJ:
                result = inferProj(e, inferOnly);
                break;

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

    /** Lean's infer_proj. */
    private Expr inferProj(Expr e, boolean inferOnly) {
        Expr type = whnf(inferTypeCore((Expr) e.o1, inferOnly));
        if (e.longVal < 0 || e.longVal > 0xFFFFFFFFL) throw invalidProj(e);   // to_proj_idx
        Object[] fa = Reducer.getAppFnArgs(type);
        Expr I = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        if (I.tag != Expr.CONST || !I.o0.equals(e.o0)) throw invalidProj(e);
        ConstantInfo ind = env.lookupOrThrow((Name) I.o0);
        if (!ind.isInduct() || ind.ctors.length != 1 || args.length != ind.numParams + ind.numIndices) throw invalidProj(e);
        ConstantInfo ctor = env.lookupOrThrow(ind.ctors[0]);
        Object[] levels = Reducer.constLevels(I);
        // instantiate_type_lparams: parameters paired with the given universes positionally
        HashMap<Object, Level> subst = new HashMap<>(ctor.levelParams.length * 2);
        for (int i = 0; i < Math.min(levels.length, ctor.levelParams.length); i++)
            subst.put(ctor.levelParams[i], (Level) levels[i]);
        Expr r = Reducer.instantiateLevelParams(ctor.type, subst);
        for (int i = 0; i < ind.numParams; i++) {
            r = whnf(r);
            if (r.tag != Expr.FORALL) throw invalidProj(e);
            r = Reducer.instantiate1((Expr) r.o2, args[i]);
        }
        boolean isPropType = isProp(type);
        long idx = e.longVal;
        for (long i = 0; i < idx; i++) {
            r = whnf(r);
            if (r.tag != Expr.FORALL) throw invalidProj(e);
            if (((Expr) r.o2).bvarRange() > 0) {
                if (isPropType && !isProp((Expr) r.o1)) throw invalidProj(e);
                r = Reducer.instantiate1((Expr) r.o2, Expr.proj(e.o0, i, (Expr) e.o1));
            } else {
                r = (Expr) r.o2;
            }
        }
        r = whnf(r);
        if (r.tag != Expr.FORALL) throw invalidProj(e);
        r = (Expr) r.o1;
        if (isPropType && !isProp(r)) throw invalidProj(e);
        return r;
    }

    private static RuntimeException invalidProj(Expr e) {
        return new RuntimeException("Type error: invalid projection " + e.o0 + "." + e.longVal);
    }

    private Expr ensureSort(Expr e) {
        Expr w = whnf(e);
        if (w.tag == Expr.SORT) return w;
        throw new RuntimeException("Type error: Expected a sort (Type/Prop)");
    }

    Expr whnfExpr(Expr e) {
        return whnf(e);
    }

    Expr ensureSortExpr(Expr e) {
        return ensureSort(e);
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
     * Lean's is_def_eq: is_def_eq_core, caching a success as an ordered pair (lean4#14806),
     * never as an equivalence class — conversion is not transitive.
     */
    public boolean isDefEq(Expr t, Expr s) {
        boolean result = isDefEqCore(t, s);
        if (result) cacheSuccess(t, s);
        return result;
    }

    // Lean's check_system(do_check_interrupted) at the head of is_def_eq_core and
    // infer_type_core: a check whose time goes into cache probes and structural comparisons
    // never reaches the reducer's fuel counter, so the interruption a timeout delivers must be
    // observed here too.
    private long systemCheckCount;
    private void checkSystem() {
        if ((++systemCheckCount & 0xFFF) == 0 && Thread.interrupted()) {
            throw new KernelAbort("Type checking interrupted (timeout)");
        }
    }

    /** Lean's quick_is_def_eq: 1 equal, -1 different, 0 not an easy case. */
    private int quickIsDefEq(Expr t, Expr s) {
        if (t == s || succeededBefore(t, s) || LeanExprKey.exprEquals(t, s)) return 1;
        boolean tLit = t.tag == Expr.LIT_NAT || t.tag == Expr.LIT_STR;
        boolean sLit = s.tag == Expr.LIT_NAT || s.tag == Expr.LIT_STR;
        if (tLit && sLit) return t.tag == s.tag && t.o0.equals(s.o0) ? 1 : -1;
        if (t.tag != s.tag) return 0;
        switch (t.tag) {
            case Expr.LAM: case Expr.FORALL: return isDefEqBinding(t, s) ? 1 : -1;
            case Expr.SORT: return Level.isEquivalent((Level) t.o0, (Level) s.o0) ? 1 : -1;
            case Expr.MDATA: return isDefEq((Expr) t.o1, (Expr) s.o1) ? 1 : -1;
            default: return 0;
        }
    }

    /**
     * Lean's is_def_eq_binding: a chain of same-kind binders; domains compared unless
     * structurally equal, a local introduced (with the right domain) only when a body uses it.
     */
    private boolean isDefEqBinding(Expr t, Expr s) {
        byte k = t.tag;
        java.util.ArrayList<Expr> subst = new java.util.ArrayList<>();
        java.util.ArrayList<Long> added = new java.util.ArrayList<>();
        try {
            do {
                Expr varSType = null;
                if (!LeanExprKey.exprEquals((Expr) t.o1, (Expr) s.o1)) {
                    varSType = instantiateRevList((Expr) s.o1, subst);
                    if (!isDefEq(instantiateRevList((Expr) t.o1, subst), varSType)) return false;
                }
                if (((Expr) t.o2).bvarRange() > 0 || ((Expr) s.o2).bvarRange() > 0) {
                    if (varSType == null) varSType = instantiateRevList((Expr) s.o1, subst);
                    long id = freshId();
                    lctxAddLocal(id, s.o0, varSType);
                    added.add(id);
                    subst.add(Expr.fvar(id));
                } else {
                    subst.add(DONT_CARE);
                }
                t = (Expr) t.o2;
                s = (Expr) s.o2;
            } while (t.tag == k && s.tag == k);
            return isDefEq(instantiateRevList(t, subst), instantiateRevList(s, subst));
        } finally {
            for (Long id : added) lctxRemove(id);
        }
    }

    private static final Expr DONT_CARE = Expr.mkConstOwned(Name.fromString("dontcare"), new Object[0]);

    private static Expr instantiateRevList(Expr e, java.util.ArrayList<Expr> subst) {
        int n = subst.size();
        if (n == 0 || e.bvarRange() == 0) return e;
        return Reducer.instantiateRev(e, n, subst.toArray(new Expr[n]), 0);
    }

    /** Lean's is_def_eq_core, phase for phase. */
    private boolean isDefEqCore(Expr t, Expr s) {
        checkSystem();
        // fuel is ours (Lean has none): a comparison of a term with itself costs nothing
        if (t != s) reducer.checkFuelPublic();
        if (++isDefEqDepth > MAX_ISDEFEQ_DEPTH)
            throw new KernelAbort("isDefEq recursion depth exceeded (" + MAX_ISDEFEQ_DEPTH + ")");
        try {
            isDefEqCalls++;
            String by = null;
            boolean r = false;
            try {
                int q = quickIsDefEq(t, s);
                if (q != 0) { by = "quick"; r = q > 0; return r; }

                // reflection: a closed term against Bool.true is fully reduced
                if ((!t.hasFVar() || eagerReduce) && isConst(s, Name.BOOL_TRUE) && isConst(whnf(t), Name.BOOL_TRUE)) {
                    by = "decide"; r = true; return r;
                }

                // whnf_core without delta, and without whnf on projected structures
                Expr tn = reducer.whnfCore(t, false, true);
                Expr sn = reducer.whnfCore(s, false, true);
                if (tn != t || sn != s) {
                    q = quickIsDefEq(tn, sn);
                    if (q != 0) { by = "quick_whnfcore"; r = q > 0; return r; }
                }

                q = isDefEqProofIrrel(tn, sn);
                if (q != 0) { by = "proof_irrel"; r = q > 0; return r; }

                Expr[] pair = {tn, sn};   // lazy_delta_reduction updates the pair even on unknown
                q = lazyDeltaReduction(pair);
                if (q != 0) { by = "lazy_delta"; r = q > 0; return r; }
                tn = pair[0];
                sn = pair[1];

                if (tn.tag == Expr.CONST && sn.tag == Expr.CONST && tn.o0.equals(sn.o0)
                        && levelsDefEq(Reducer.constLevels(tn), Reducer.constLevels(sn))) {
                    by = "const_eq"; r = true; return r;
                }
                if (tn.tag == Expr.FVAR && sn.tag == Expr.FVAR && tn.longVal == sn.longVal) {
                    by = "fvar_eq"; r = true; return r;
                }
                if (tn.tag == Expr.PROJ && sn.tag == Expr.PROJ && tn.o0.equals(sn.o0) && tn.longVal == sn.longVal) {
                    Expr[] structs = {(Expr) tn.o1, (Expr) sn.o1};
                    if (lazyDeltaProjReduction(structs, (Name) tn.o0, tn.longVal)) { by = "proj_delta"; r = true; return r; }
                }

                // whnf_core again, now reducing projected structures with whnf
                Expr tnn = reducer.whnfCore(tn);
                Expr snn = reducer.whnfCore(sn);
                if (tnn != tn || snn != sn) { by = "whnfcore2"; r = isDefEqCore(tnn, snn); return r; }

                if (isDefEqApp(tn, sn)) { by = "app"; r = true; return r; }
                if (tryEtaExpansion(tn, sn)) { by = "eta"; r = true; return r; }
                if (tryEtaStruct(tn, sn)) { by = "eta_struct"; r = true; return r; }
                q = tryStringLitExpansion(tn, sn);
                if (q != 0) { by = "string_lit"; r = q > 0; return r; }
                if (isDefEqUnitLike(tn, sn)) { by = "unit_like"; r = true; return r; }
                by = "fail";
                return false;
            } finally {
                if (by != null && traceWriter != null) emitTrace(exprFingerprint(t), exprFingerprint(s), r, by);
                if (tracing && by != null) trace("isDefEq d=" + isDefEqDepth + " " + exprSummary(t, 3) + " =?= " + exprSummary(s, 3) + " => " + r + " (" + by + ")");
            }
        } finally {
            isDefEqDepth--;
        }
    }

    private static boolean isConst(Expr e, Name n) {
        return e.tag == Expr.CONST && n.equals(e.o0);
    }

    /** Lean's is_def_eq(levels, levels): pointwise is_equivalent. */
    private static boolean levelsDefEq(Object[] a, Object[] b) {
        if (a.length != b.length) return false;
        for (int i = 0; i < a.length; i++)
            if (!Level.isEquivalent((Level) a[i], (Level) b[i])) return false;
        return true;
    }

    /** Lean's is_def_eq_proof_irrel. Inference errors propagate, as in Lean. */
    private int isDefEqProofIrrel(Expr t, Expr s) {
        Expr tType = inferTypeOnly(t);
        if (!isProp(tType)) return 0;
        return isDefEq(tType, inferTypeOnly(s)) ? 1 : -1;
    }

    /** Lean's is_nat_zero: the constant Nat.zero or the literal 0. */
    private static boolean isNatZero(Expr e) {
        return Reducer.isNatZeroConst(e) || (e.tag == Expr.LIT_NAT && ((BigInteger) e.o0).signum() == 0);
    }

    /** Lean's is_nat_succ: the predecessor of a positive literal or of `Nat.succ x`. */
    private static Expr natSucc(Expr e) {
        if (e.tag == Expr.LIT_NAT) {
            BigInteger v = (BigInteger) e.o0;
            return v.signum() > 0 ? Expr.litNat(v.subtract(BigInteger.ONE)) : null;
        }
        if (e.tag == Expr.APP && Reducer.isNatSuccConst((Expr) e.o0)) return (Expr) e.o1;
        return null;
    }

    /** Lean's is_def_eq_offset. */
    private int isDefEqOffset(Expr t, Expr s) {
        if (isNatZero(t) && isNatZero(s)) return 1;
        Expr pt = natSucc(t), ps = natSucc(s);
        if (pt != null && ps != null) return isDefEqCore(pt, ps) ? 1 : -1;
        return 0;
    }

    /**
     * Lean's lazy_delta_reduction: until a step decides, the Nat offset rule, native Nat
     * reduction on closed terms, then one lazy unfolding step. The pair is the caller's own
     * and is updated in place, also when the answer is unknown.
     */
    private int lazyDeltaReduction(Expr[] pair) {
        while (true) {
            int r = isDefEqOffset(pair[0], pair[1]);
            if (r != 0) return r;
            if ((!pair[0].hasFVar() && !pair[1].hasFVar()) || eagerReduce) {
                Expr tv = reducer.reduceNat(pair[0]);
                if (tv != null) return isDefEqCore(tv, pair[1]) ? 1 : -1;
                Expr sv = reducer.reduceNat(pair[1]);
                if (sv != null) return isDefEqCore(pair[0], sv) ? 1 : -1;
            }
            int step = lazyDeltaReductionStep(pair);
            if (step != CONTINUE) return step;
        }
    }

    private static final int CONTINUE = 2;   // reduction_status::Continue; 1/-1/0 = equal/diff/unknown

    /** Lean's lazy_delta_proj_reduction for `t.idx =?= s.idx` over the same structure. */
    private boolean lazyDeltaProjReduction(Expr[] pair, Name sname, long idx) {
        while (true) {
            int step = lazyDeltaReductionStep(pair);
            if (step == 1) return true;
            if (step != CONTINUE) {
                Expr t = reducer.reduceProjCore(pair[0], sname, idx);
                if (t != null) {
                    Expr s = reducer.reduceProjCore(pair[1], sname, idx);
                    if (s != null) return isDefEqCore(t, s);
                }
                return isDefEqCore(pair[0], pair[1]);
            }
        }
    }

    /**
     * Lean's lazy_delta_reduction_step: unfold the side with the greater definitional height
     * (both on a tie; first trying the arguments when both are the same regular definition),
     * then the quick check. Returns 1/-1/0 (equal, different, unknown) or CONTINUE.
     */
    private int lazyDeltaReductionStep(Expr[] pair) {
        Expr tn = pair[0], sn = pair[1];
        ConstantInfo dt = deltaInfo(tn), ds = deltaInfo(sn);
        if (dt == null && ds == null) return 0;
        if (dt != null && ds == null) {
            Expr s2 = tryUnfoldProjApp(sn);
            if (s2 != null) sn = s2; else tn = unfoldWhnfCore(tn);
        } else if (dt == null) {
            Expr t2 = tryUnfoldProjApp(tn);
            if (t2 != null) tn = t2; else sn = unfoldWhnfCore(sn);
        } else {
            int c = compareHints(dt.getHintsCode(), ds.getHintsCode());
            if (c < 0) {
                tn = unfoldWhnfCore(tn);
            } else if (c > 0) {
                sn = unfoldWhnfCore(sn);
            } else {
                if (tn.tag == Expr.APP && sn.tag == Expr.APP && sameDeclaration(dt, ds) && dt.getHintsCode() >= 0
                        && !failedBefore(tn, sn)) {
                    if (levelsDefEq(Reducer.constLevels(Reducer.getAppFn(tn)), Reducer.constLevels(Reducer.getAppFn(sn)))
                            && isDefEqArgs(tn, sn)) {
                        return 1;
                    }
                    cacheFailure(tn, sn);
                }
                tn = unfoldWhnfCore(tn);
                sn = unfoldWhnfCore(sn);
            }
        }
        pair[0] = tn;
        pair[1] = sn;
        int q = quickIsDefEq(tn, sn);
        return q != 0 ? q : CONTINUE;
    }

    /** whnf_core(unfold_definition(e), cheap_proj): e's head is a delta candidate. */
    private Expr unfoldWhnfCore(Expr e) {
        return reducer.whnfCore(reducer.unfoldDefinition(e), false, true);
    }

    /** Lean's try_unfold_proj_app: e is `s.i args` and whnf_core changes it. */
    private Expr tryUnfoldProjApp(Expr e) {
        if (Reducer.getAppFn(e).tag != Expr.PROJ) return null;
        Expr n = reducer.whnfCore(e);
        return LeanExprKey.exprEquals(n, e) ? null : n;
    }

    /**
     * Lean's `is_eqp(*d_t, *d_s)`: the two heads resolve to the same declaration. Lean's
     * environment hands out one constant_info per name; here a lookup can re-materialize a
     * declaration whose soft-referenced cache entry was collected, so the test is by name.
     */
    private static boolean sameDeclaration(ConstantInfo a, ConstantInfo b) {
        return a == b || a.name.equals(b.name);
    }

    /** Lean's is_delta: the head is a constant with a value, applied to its universe arity
     *  (and, in a restricted-transparency checker, one the reducer may unfold). */
    private ConstantInfo deltaInfo(Expr e) {
        Expr head = Reducer.getAppFn(e);
        if (head.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || ci.getValue() == null || ci.levelParams.length != Reducer.constLevels(head).length) return null;
        return reducer.canUnfold((Name) head.o0) ? ci : null;
    }

    /** Lean's compare(hints): < 0 unfold t, > 0 unfold s, 0 both. */
    private static int compareHints(long t, long s) {
        if (t == ConstantInfo.REDUCIBILITY_OPAQUE && s == ConstantInfo.REDUCIBILITY_OPAQUE) return 0;
        if (t == ConstantInfo.REDUCIBILITY_OPAQUE) return 1;
        if (s == ConstantInfo.REDUCIBILITY_OPAQUE) return -1;
        if (t == ConstantInfo.REDUCIBILITY_ABBREV && s >= 0) return -1;
        if (s == ConstantInfo.REDUCIBILITY_ABBREV && t >= 0) return 1;
        if (t == ConstantInfo.REDUCIBILITY_ABBREV && s == ConstantInfo.REDUCIBILITY_ABBREV) return 0;
        return Long.compare(s, t);   // both regular: the greater height unfolds first
    }

    // type_checker.cpp: the pair is stored hash-ordered, looked up symmetrically on a hash tie;
    // one ordered pair, never an equivalence class (lean4#14806).
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

    /** Lean's is_def_eq_app: equal heads and pointwise equal arguments. */
    private boolean isDefEqApp(Expr t, Expr s) {
        if (t.tag != Expr.APP || s.tag != Expr.APP) return false;
        Object[] tfa = Reducer.getAppFnArgs(t), sfa = Reducer.getAppFnArgs(s);
        Expr[] tArgs = (Expr[]) tfa[1], sArgs = (Expr[]) sfa[1];
        if (!isDefEq((Expr) tfa[0], (Expr) sfa[0]) || tArgs.length != sArgs.length) return false;
        for (int i = 0; i < tArgs.length; i++)
            if (!isDefEq(tArgs[i], sArgs[i])) return false;
        return true;
    }

    /** Lean's is_def_eq_args: arguments from the outermost application inward. */
    private boolean isDefEqArgs(Expr t, Expr s) {
        while (t.tag == Expr.APP && s.tag == Expr.APP) {
            if (!isDefEq((Expr) t.o1, (Expr) s.o1)) return false;
            t = (Expr) t.o0;
            s = (Expr) s.o0;
        }
        return t.tag != Expr.APP && s.tag != Expr.APP;
    }

    /** Lean's try_eta_expansion (both directions). */
    private boolean tryEtaExpansion(Expr t, Expr s) {
        return tryEtaExpansionCore(t, s) || tryEtaExpansionCore(s, t);
    }

    private boolean tryEtaExpansionCore(Expr t, Expr s) {
        if (t.tag != Expr.LAM || s.tag == Expr.LAM) return false;
        Expr sType = whnf(inferTypeOnly(s));
        if (sType.tag != Expr.FORALL) return false;
        return isDefEq(t, Expr.lam(sType.o0, (Expr) sType.o1, Expr.app(Reducer.lift(s, 1, 0), Expr.bvar(0)), sType.o3));
    }

    /** Lean's is_non_rec_structure: one constructor, no indices, not recursive. */
    private boolean isNonRecStructure(Name n) {
        ConstantInfo ci = env.lookup(n);
        return ci != null && ci.isInduct() && ci.ctors.length == 1 && ci.numIndices == 0 && !ci.isRec;
    }

    /** Lean's try_eta_struct (both directions). */
    private boolean tryEtaStruct(Expr t, Expr s) {
        return tryEtaStructCore(t, s) || tryEtaStructCore(s, t);
    }

    /** Lean's try_eta_struct_core: s is `mk ps fs` of a non-recursive structure and t.i =?= fs_i. */
    private boolean tryEtaStructCore(Expr t, Expr s) {
        Expr f = Reducer.getAppFn(s);
        if (f.tag != Expr.CONST) return false;
        ConstantInfo ctor = env.lookupOrThrow((Name) f.o0);
        if (!ctor.isCtor()) return false;
        Expr[] sArgs = (Expr[]) Reducer.getAppFnArgs(s)[1];
        if (sArgs.length != ctor.numParams + ctor.numFields) return false;
        if (!isNonRecStructure(ctor.inductName)) return false;
        if (!isDefEq(inferTypeOnly(t), inferTypeOnly(s))) return false;
        for (int i = ctor.numParams; i < sArgs.length; i++)
            if (!isDefEq(Expr.proj(ctor.inductName, i - ctor.numParams, t), sArgs[i])) return false;
        return true;
    }

    /** Lean's try_string_lit_expansion: a literal against exactly `String.ofList xs`. */
    private int tryStringLitExpansion(Expr t, Expr s) {
        int r = tryStringLitExpansionCore(t, s);
        return r != 0 ? r : tryStringLitExpansionCore(s, t);
    }

    private int tryStringLitExpansionCore(Expr t, Expr s) {
        if (t.tag == Expr.LIT_STR && s.tag == Expr.APP && Reducer.isConst0((Expr) s.o0, Name.STRING_OF_LIST))
            return isDefEqCore(whnf(Reducer.stringLitToConstructor(t)), s) ? 1 : -1;
        return 0;
    }

    /** Lean's is_def_eq_unit_like: both of a non-recursive structure type without fields. */
    private boolean isDefEqUnitLike(Expr t, Expr s) {
        Expr tType = whnf(inferTypeOnly(t));
        Expr I = Reducer.getAppFn(tType);
        if (I.tag != Expr.CONST || !isNonRecStructure((Name) I.o0)) return false;
        ConstantInfo ctor = env.lookupOrThrow(env.lookupOrThrow((Name) I.o0).ctors[0]);
        if (ctor.numFields != 0) return false;
        return isDefEqCore(tType, inferTypeOnly(s));
    }


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
}
