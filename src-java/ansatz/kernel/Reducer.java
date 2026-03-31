// Ansatz kernel — WHNF reduction engine.

package ansatz.kernel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;

/**
 * WHNF (Weak Head Normal Form) reduction engine.
 * Port of reduce.clj with caches matching Lean 4's type_checker.cpp.
 *
 * <p>Caches:
 * <ul>
 *   <li>whnfCoreCache — expr → whnf_core result (when not cheap)
 *   <li>whnfCache — expr → full whnf result
 *   <li>unfoldCache — const-with-levels → unfolded body
 * </ul>
 */
public final class Reducer {

    private final Env env;
    private final IdentityHashMap<Expr, Expr> whnfCoreCache;
    private final IdentityHashMap<Expr, Expr> whnfCache;
    private final IdentityHashMap<Expr, Expr> unfoldCache;
    private final HashMap<Expr, Expr> resultIntern;  // result deduplication for pointer sharing

    // Local context: fvar id -> LocalDecl
    // Managed externally (from TypeChecker)
    private HashMap<Long, Object[]> lctx; // [0]=tag(0=local,1=let), [1]=name, [2]=type, [3]=value(let only)

    // Fuel tracking
    private long fuel;
    private long initialFuel;
    private static final long DEFAULT_FUEL = 5_000_000L;

    // ---- Instrumentation counters ----
    long betaCount;      // beta reductions (lambda application)
    long deltaCount;     // delta unfoldings (definition unfolding)
    long iotaCount;      // iota reductions (recursor/quot)
    long zetaCount;      // zeta reductions (let substitution)
    long mdataCount;     // mdata stripping
    long fvarLetCount;   // fvar let-unfolding
    long projCount;      // projection reduction (counted externally in whnfCoreImpl)
    long whnfCalls;      // total whnf() calls
    long whnfCoreCacheHits;  // whnfCore cache hits
    long whnfCacheHits;      // whnf cache hits
    long internHits;         // result intern hits (pointer sharing)
    int whnfDepth;           // current recursion depth
    int whnfMaxDepth;        // max recursion depth seen
    Expr whnfMaxDepthExpr;   // expression at max depth
    Expr whnfFirstDeepExpr;  // first expression at depth 100
    StackTraceElement[] whnfFirstDeepStack;  // stack trace at depth 100

    // Ring buffer trace: last N operations
    private static final int TRACE_RING_SIZE = 1024;
    private final String[] traceRing = new String[TRACE_RING_SIZE];
    private int traceRingPos = 0;
    private long traceSeq = 0; // monotonic sequence number

    // Transparency mode (Lean 4: reducible < instances < default < all)
    // 0 = reducible only (most restrictive — for equation theorem generation)
    // 1 = default (normal — unfolds non-opaque definitions)
    // 2 = all (least restrictive — unfolds everything including opaque)
    // Default: 1 (same as current behavior)
    private int transparencyMode = 1;

    /** Set the transparency mode for WHNF delta reduction.
     *  0 = reducible (never unfold user definitions — for equation theorem gen)
     *  1 = default (normal behavior — unfold definitions)
     *  2 = all (unfold everything)
     *  Names in deltaAllowSet are always unfolded regardless of mode. */
    public void setTransparency(int mode) {
        this.transparencyMode = mode;
        // Clear caches since reduction behavior changes
        this.whnfCoreCache.clear();
        this.whnfCache.clear();
        this.unfoldCache.clear();
    }

    public int getTransparency() { return transparencyMode; }

    // When transparencyMode=0 (reducible), ONLY unfold names in this set
    private java.util.HashSet<Name> deltaAllowSet = null;

    /** Set the allow-list for reducible mode. Only these names will be delta-reduced
     *  when transparency=0. Pass null to clear. */
    public void setDeltaAllowSet(java.util.HashSet<Name> names) {
        this.deltaAllowSet = names;
    }

    // Callbacks for K-recursor support
    private InferFn inferFn;
    private IsDefEqFn isDefEqFn;

    @FunctionalInterface
    public interface InferFn {
        Expr infer(Expr e);
    }

    @FunctionalInterface
    public interface IsDefEqFn {
        boolean isDefEq(Expr a, Expr b);
    }

    public Reducer(Env env) {
        this.env = env;
        this.whnfCoreCache = new IdentityHashMap<>(4096);
        this.whnfCache = new IdentityHashMap<>(4096);
        this.unfoldCache = new IdentityHashMap<>(1024);
        this.resultIntern = new HashMap<>(4096);
        this.lctx = null;
        this.fuel = DEFAULT_FUEL;
        this.initialFuel = DEFAULT_FUEL;
    }

    /** Set fuel limit. 0 means unlimited (no fuel checking). */
    public void setFuel(long fuel) { this.fuel = fuel; this.initialFuel = fuel; }
    public long getFuelUsed() { return initialFuel > 0 ? initialFuel - fuel : -fuel; }
    public void setLctx(HashMap<Long, Object[]> lctx) { this.lctx = lctx; }
    public void setCallbacks(InferFn inferFn, IsDefEqFn isDefEqFn) {
        this.inferFn = inferFn;
        this.isDefEqFn = isDefEqFn;
    }

    public HashMap<Long, Object[]> getLctx() { return lctx; }

    /**
     * Intern a whnf result: return the canonical instance for structurally equal expressions.
     * This enables reference equality (==) short-circuits in isDefEq, mirroring Lean 4's
     * pointer sharing from hash-consing.
     */
    public Expr internResult(Expr r) {
        // No size limit — grows per declaration, freed on clearCaches().
        // Clearing destroys pointer sharing needed by IdentityHashMap caches.
        Expr existing = resultIntern.putIfAbsent(r, r);
        if (existing != null) { internHits++; return existing; }
        return r;
    }

    // ============================================================
    // de Bruijn operations
    // ============================================================

    /**
     * Lift (shift) free de Bruijn indices in e by d, starting from cutoff c.
     */
    public static Expr lift(Expr e, int d, int c) {
        return liftGo(e, d, c, new ArrayList<>());
    }

    private static IdentityHashMap<Expr, Expr> getDepthCache(ArrayList<IdentityHashMap<Expr, Expr>> caches, int depth) {
        while (caches.size() <= depth) caches.add(null);
        IdentityHashMap<Expr, Expr> m = caches.get(depth);
        if (m == null) { m = new IdentityHashMap<>(); caches.set(depth, m); }
        return m;
    }

    private static Expr liftGo(Expr e, int d, int c, ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (e.bvarRange() <= c) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, c);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: {
                long idx = e.longVal;
                result = idx >= c ? Expr.bvar(idx + d) : e;
                break;
            }
            case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR: case Expr.FVAR:
                return e;
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.bvarRange() > c) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = liftGo(cur, d, c, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = liftGo(origArg, d, c, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = liftGo((Expr) e.o1, d, c, caches);
                Expr newBody = liftGo((Expr) e.o2, d, c + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = liftGo((Expr) e.o1, d, c, caches);
                Expr newBody = liftGo((Expr) e.o2, d, c + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = liftGo((Expr) e.o1, d, c, caches);
                Expr newVal = liftGo((Expr) e.o2, d, c, caches);
                Expr newBody = liftGo((Expr) e.o3, d, c + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = liftGo((Expr) e.o1, d, c, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = liftGo((Expr) e.o1, d, c, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    /**
     * Replace (bvar 0) with val in e, shifting remaining bvars down.
     */
    public static Expr instantiate1(Expr e, Expr val) {
        return instantiate1Go(e, val, 0, new ArrayList<>());
    }

    /**
     * Batch instantiate: replace bvar(0)..bvar(n-1) with subst[0..n-1] in a single pass.
     * Matching Lean 4's instantiate(body, n, subst) — avoids O(n) traversals.
     * subst array is in APPLICATION order: subst[0] replaces bvar(n-1), subst[n-1] replaces bvar(0).
     * (This matches Lean 4's instantiate_rev semantics used in whnf beta reduction.)
     */
    public static Expr instantiateRev(Expr e, int n, Expr[] subst, int substOffset) {
        if (n == 0 || e.bvarRange() == 0) return e;
        if (n == 1) return instantiate1(e, subst[substOffset]);
        return instantiateRevGo(e, n, subst, substOffset, 0, new ArrayList<>());
    }

    private static Expr instantiateRevGo(Expr e, int n, Expr[] subst, int substOffset, int depth,
                                          ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (e.bvarRange() <= depth) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, depth);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: {
                long idx = e.longVal;
                if (idx >= depth && idx < depth + n) {
                    int k = (int)(idx - depth);
                    result = lift(subst[substOffset + n - 1 - k], depth, 0);
                } else if (idx >= depth + n) {
                    result = Expr.bvar(idx - n);
                } else {
                    return e;
                }
                break;
            }
            case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR: case Expr.FVAR:
                return e;
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.bvarRange() > depth) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = instantiateRevGo(cur, n, subst, substOffset, depth, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = instantiateRevGo(origArg, n, subst, substOffset, depth, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = instantiateRevGo((Expr) e.o1, n, subst, substOffset, depth, caches);
                Expr newBody = instantiateRevGo((Expr) e.o2, n, subst, substOffset, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = instantiateRevGo((Expr) e.o1, n, subst, substOffset, depth, caches);
                Expr newBody = instantiateRevGo((Expr) e.o2, n, subst, substOffset, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = instantiateRevGo((Expr) e.o1, n, subst, substOffset, depth, caches);
                Expr newVal = instantiateRevGo((Expr) e.o2, n, subst, substOffset, depth, caches);
                Expr newBody = instantiateRevGo((Expr) e.o3, n, subst, substOffset, depth + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = instantiateRevGo((Expr) e.o1, n, subst, substOffset, depth, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = instantiateRevGo((Expr) e.o1, n, subst, substOffset, depth, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    private static Expr instantiate1Go(Expr e, Expr val, int depth, ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (e.bvarRange() <= depth) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, depth);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: {
                long idx = e.longVal;
                if (idx == depth) { result = lift(val, depth, 0); break; }
                if (idx > depth) { result = Expr.bvar(idx - 1); break; }
                return e;
            }
            case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR: case Expr.FVAR:
                return e;
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.bvarRange() > depth) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = instantiate1Go(cur, val, depth, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = instantiate1Go(origArg, val, depth, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = instantiate1Go((Expr) e.o1, val, depth, caches);
                Expr newBody = instantiate1Go((Expr) e.o2, val, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = instantiate1Go((Expr) e.o1, val, depth, caches);
                Expr newBody = instantiate1Go((Expr) e.o2, val, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = instantiate1Go((Expr) e.o1, val, depth, caches);
                Expr newVal = instantiate1Go((Expr) e.o2, val, depth, caches);
                Expr newBody = instantiate1Go((Expr) e.o3, val, depth + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = instantiate1Go((Expr) e.o1, val, depth, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = instantiate1Go((Expr) e.o1, val, depth, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    /**
     * Cheap beta reduction: (fun x => body) a1 a2 ... → body[x:=a1] a2 ...
     * Only handles cases where the result doesn't require full substitution.
     * Matching Lean 4's cheap_beta_reduce (instantiate.cpp:211-230).
     */
    public static Expr cheapBetaReduce(Expr e) {
        if (e.tag != Expr.APP) return e;
        // Collect app spine
        java.util.ArrayList<Expr> args = new java.util.ArrayList<>();
        Expr fn = e;
        while (fn.tag == Expr.APP) {
            args.add((Expr) fn.o1);
            fn = (Expr) fn.o0;
        }
        if (fn.tag != Expr.LAM) return e;
        // Strip lambdas matching args (args are reversed)
        int i = 0;
        int nargs = args.size();
        while (fn.tag == Expr.LAM && i < nargs) {
            i++;
            fn = (Expr) fn.o2; // binding_body
        }
        if (fn.bvarRange() == 0) {
            // Body has no loose bvars — just apply remaining args
            Expr result = fn;
            for (int j = nargs - i - 1; j >= 0; j--) {
                result = Expr.app(result, args.get(j));
            }
            return result;
        } else if (fn.tag == Expr.BVAR) {
            // Body is a single bvar reference
            int idx = (int) fn.longVal;
            if (idx < i) {
                // bvar(idx) maps to args[nargs - (i - idx)] = args[nargs - i + idx]
                Expr result = args.get(nargs - i + idx);
                for (int j = nargs - i - 1; j >= 0; j--) {
                    result = Expr.app(result, args.get(j));
                }
                return result;
            }
        }
        return e;
    }

    /**
     * Replace free occurrences of fvar(fvId) with bvar(depth).
     */
    public static Expr abstract1(Expr e, long fvId) {
        if (!e.hasFVar()) return e;
        return abstract1Go(e, fvId, 0, new ArrayList<>());
    }

    private static Expr abstract1Go(Expr e, long fvId, int depth, ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (!e.hasFVar()) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, depth);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR:
                return e;
            case Expr.FVAR:
                result = e.longVal == fvId ? Expr.bvar(depth) : e;
                break;
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.hasFVar()) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = abstract1Go(cur, fvId, depth, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = abstract1Go(origArg, fvId, depth, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = abstract1Go((Expr) e.o1, fvId, depth, caches);
                Expr newBody = abstract1Go((Expr) e.o2, fvId, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = abstract1Go((Expr) e.o1, fvId, depth, caches);
                Expr newBody = abstract1Go((Expr) e.o2, fvId, depth + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = abstract1Go((Expr) e.o1, fvId, depth, caches);
                Expr newVal = abstract1Go((Expr) e.o2, fvId, depth, caches);
                Expr newBody = abstract1Go((Expr) e.o3, fvId, depth + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = abstract1Go((Expr) e.o1, fvId, depth, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = abstract1Go((Expr) e.o1, fvId, depth, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    /**
     * Abstract multiple fvars simultaneously, matching Lean 4's abstract(e, n, subst).
     * fvarIds[i] gets replaced with bvar(offset + n - i - 1).
     */
    public static Expr abstractFvars(Expr e, int n, long[] fvarIds) {
        if (!e.hasFVar() || n == 0) return e;
        return abstractFvarsGo(e, n, fvarIds, 0, new ArrayList<>());
    }

    private static Expr abstractFvarsGo(Expr e, int n, long[] fvarIds, int offset,
                                         ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (!e.hasFVar()) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, offset);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR:
                return e;
            case Expr.FVAR: {
                int i = n;
                while (i > 0) {
                    --i;
                    if (fvarIds[i] == e.longVal) {
                        result = Expr.bvar(offset + n - i - 1);
                        dc.put(e, result);
                        return result;
                    }
                }
                return e;
            }
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.hasFVar()) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = abstractFvarsGo(cur, n, fvarIds, offset, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = abstractFvarsGo(origArg, n, fvarIds, offset, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = abstractFvarsGo((Expr) e.o1, n, fvarIds, offset, caches);
                Expr newBody = abstractFvarsGo((Expr) e.o2, n, fvarIds, offset + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = abstractFvarsGo((Expr) e.o1, n, fvarIds, offset, caches);
                Expr newBody = abstractFvarsGo((Expr) e.o2, n, fvarIds, offset + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = abstractFvarsGo((Expr) e.o1, n, fvarIds, offset, caches);
                Expr newVal = abstractFvarsGo((Expr) e.o2, n, fvarIds, offset, caches);
                Expr newBody = abstractFvarsGo((Expr) e.o3, n, fvarIds, offset + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = abstractFvarsGo((Expr) e.o1, n, fvarIds, offset, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = abstractFvarsGo((Expr) e.o1, n, fvarIds, offset, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    /**
     * Lower loose bvar indices >= s by d. Matching Lean's lower_loose_bvars.
     * Used when removing dead let bindings in mkBinding.
     */
    public static Expr lowerLooseBVars(Expr e, int s, int d) {
        if (e.bvarRange() <= s) return e;
        return lowerLooseBVarsGo(e, s, d, 0, new ArrayList<>());
    }

    private static Expr lowerLooseBVarsGo(Expr e, int s, int d, int offset,
                                           ArrayList<IdentityHashMap<Expr, Expr>> caches) {
        if (e.bvarRange() <= offset) return e;
        IdentityHashMap<Expr, Expr> dc = getDepthCache(caches, offset);
        Expr cached = dc.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case Expr.BVAR: {
                long idx = e.longVal;
                result = (idx >= offset + s) ? Expr.bvar(idx - d) : e;
                break;
            }
            case Expr.SORT: case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR: case Expr.FVAR:
                return e;
            case Expr.APP: {
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.bvarRange() > offset) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = lowerLooseBVarsGo(cur, s, d, offset, caches);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = lowerLooseBVarsGo(origArg, s, d, offset, caches);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = lowerLooseBVarsGo((Expr) e.o1, s, d, offset, caches);
                Expr newBody = lowerLooseBVarsGo((Expr) e.o2, s, d, offset + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = lowerLooseBVarsGo((Expr) e.o1, s, d, offset, caches);
                Expr newBody = lowerLooseBVarsGo((Expr) e.o2, s, d, offset + 1, caches);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.LET: {
                Expr newType = lowerLooseBVarsGo((Expr) e.o1, s, d, offset, caches);
                Expr newVal = lowerLooseBVarsGo((Expr) e.o2, s, d, offset, caches);
                Expr newBody = lowerLooseBVarsGo((Expr) e.o3, s, d, offset + 1, caches);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = lowerLooseBVarsGo((Expr) e.o1, s, d, offset, caches);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = lowerLooseBVarsGo((Expr) e.o1, s, d, offset, caches);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default: return e;
        }
        dc.put(e, result);
        return result;
    }

    /**
     * Instantiate universe level params in an expression.
     * Uses identity-based memoization for DAG-structured expressions.
     */
    public static Expr instantiateLevelParams(Expr e, HashMap<Object, Level> subst) {
        if (subst.isEmpty() || !e.hasLevelParam()) return e;
        IdentityHashMap<Expr, Expr> cache = new IdentityHashMap<>();
        return instantiateLPGo(e, subst, cache);
    }

    private static Expr instantiateLPGo(Expr e, HashMap<Object, Level> subst, IdentityHashMap<Expr, Expr> cache) {
        if (!e.hasLevelParam()) return e;
        Expr cached = cache.get(e);
        if (cached != null) return cached;

        Expr result;
        switch (e.tag) {
            case Expr.BVAR: case Expr.LIT_NAT: case Expr.LIT_STR: case Expr.FVAR:
                result = e;
                break;
            case Expr.SORT: {
                Level newLvl = Level.instantiate((Level) e.o0, subst);
                result = (newLvl == e.o0) ? e : Expr.sort(newLvl, Level.hasParam(newLvl));
                break;
            }
            case Expr.CONST: {
                @SuppressWarnings("unchecked")
                Object levels = e.o1;
                if (levels instanceof Object[]) {
                    Object[] lvls = (Object[]) levels;
                    Level[] newLvls = new Level[lvls.length];
                    boolean anyChanged = false;
                    boolean anyParam = false;
                    for (int i = 0; i < lvls.length; i++) {
                        newLvls[i] = Level.instantiate((Level) lvls[i], subst);
                        anyChanged = anyChanged || (newLvls[i] != lvls[i]);
                        anyParam = anyParam || Level.hasParam(newLvls[i]);
                    }
                    result = anyChanged ? Expr.mkConst(e.o0, newLvls, anyParam) : e;
                } else {
                    Object[] lvlArr = constLevels(e);
                    Object[] newLvls = new Object[lvlArr.length];
                    boolean anyChanged = false;
                    boolean anyParam = false;
                    for (int i = 0; i < lvlArr.length; i++) {
                        newLvls[i] = Level.instantiate((Level) lvlArr[i], subst);
                        anyChanged = anyChanged || (newLvls[i] != lvlArr[i]);
                        anyParam = anyParam || Level.hasParam((Level) newLvls[i]);
                    }
                    if (!anyChanged) {
                        result = e;
                    } else {
                        Object newLevelsObj;
                        if (levels instanceof clojure.lang.IPersistentVector) {
                            newLevelsObj = clojure.lang.PersistentVector.create(newLvls);
                        } else {
                            newLevelsObj = java.util.Arrays.asList(newLvls);
                        }
                        result = Expr.mkConst(e.o0, newLevelsObj, anyParam);
                    }
                }
                break;
            }
            case Expr.APP: {
                // Iterative APP traversal — avoids stack overflow on deep expression trees.
                // Collect the APP spine, instantiate head, then process args iteratively.
                int n = 0;
                Expr cur = e;
                while (cur.tag == Expr.APP) { n++; cur = (Expr) cur.o0; }
                // cur is now the head (non-APP)
                Expr newHead = cur.hasLevelParam() ? instantiateLPGo(cur, subst, cache) : cur;
                // Process args iteratively (no recursive instantiateLPGo for args)
                Expr[] origArgs = new Expr[n];
                Expr tmpCur = e;
                for (int i = n - 1; i >= 0; i--) {
                    origArgs[i] = (Expr) tmpCur.o1;
                    tmpCur = (Expr) tmpCur.o0;
                }
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = 0; i < n; i++) {
                    Expr origArg = origArgs[i];
                    Expr newArg = origArg.hasLevelParam() ? instantiateLPGo(origArg, subst, cache) : origArg;
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM:
            case Expr.FORALL: {
                // Iterative traversal of nested LAM/FORALL chains to avoid stack overflow.
                // Collect the chain, process types, then rebuild from inside out.
                java.util.ArrayList<Expr> chain = new java.util.ArrayList<>();
                Expr cur2 = e;
                while ((cur2.tag == Expr.LAM || cur2.tag == Expr.FORALL) && cur2.hasLevelParam()) {
                    chain.add(cur2);
                    cur2 = (Expr) cur2.o2; // body
                }
                // Process the innermost body
                Expr newInner = cur2.hasLevelParam() ? instantiateLPGo(cur2, subst, cache) : cur2;
                boolean changed = (newInner != cur2);
                // Rebuild from inside out
                Expr rebuilt = newInner;
                for (int i = chain.size() - 1; i >= 0; i--) {
                    Expr node = chain.get(i);
                    Expr newType = ((Expr) node.o1).hasLevelParam() ?
                        instantiateLPGo((Expr) node.o1, subst, cache) : (Expr) node.o1;
                    changed = changed || (newType != node.o1) || (rebuilt != node.o2);
                    rebuilt = node.tag == Expr.LAM ?
                        Expr.lam(node.o0, newType, rebuilt, node.o3) :
                        Expr.forall(node.o0, newType, rebuilt, node.o3);
                }
                result = changed ? rebuilt : e;
                break;
            }
            case Expr.LET: {
                Expr newType = instantiateLPGo((Expr) e.o1, subst, cache);
                Expr newVal = instantiateLPGo((Expr) e.o2, subst, cache);
                Expr newBody = instantiateLPGo((Expr) e.o3, subst, cache);
                result = (newType == e.o1 && newVal == e.o2 && newBody == e.o3) ? e : Expr.mkLet(e.o0, newType, newVal, newBody);
                break;
            }
            case Expr.MDATA: {
                Expr newE = instantiateLPGo((Expr) e.o1, subst, cache);
                result = (newE == e.o1) ? e : Expr.mdata(e.o0, newE);
                break;
            }
            case Expr.PROJ: {
                Expr newE = instantiateLPGo((Expr) e.o1, subst, cache);
                result = (newE == e.o1) ? e : Expr.proj(e.o0, e.longVal, newE);
                break;
            }
            default:
                result = e;
        }
        cache.put(e, result);
        return result;
    }

    // ============================================================
    // App spine utilities
    // ============================================================

    /** Get the head function of nested applications. */
    public static Expr getAppFn(Expr e) {
        while (e.tag == Expr.APP) e = (Expr) e.o0;
        return e;
    }

    /** Get [head, args] from nested applications. */
    private static final Expr[] EMPTY_EXPR_ARRAY = new Expr[0];

    /** Decompose application into head + args. No ArrayList — direct array allocation.
     *  Matching Lean 4's get_app_args which uses a stack-allocated buffer. */
    public static Object[] getAppFnArgs(Expr e) {
        if (e.tag != Expr.APP) return new Object[]{e, EMPTY_EXPR_ARRAY};
        // Count args first (avoids ArrayList)
        int n = 0;
        Expr fn = e;
        while (fn.tag == Expr.APP) { n++; fn = (Expr) fn.o0; }
        // Fill array directly (reverse order)
        Expr[] argsArr = new Expr[n];
        Expr cur = e;
        for (int i = n - 1; i >= 0; i--) {
            argsArr[i] = (Expr) cur.o1;
            cur = (Expr) cur.o0;
        }
        return new Object[]{fn, argsArr};
    }

    /** Build app from head and args array. */
    public static Expr mkApps(Expr head, Expr[] args) {
        Expr result = head;
        for (Expr arg : args) result = Expr.app(result, arg);
        return result;
    }

    /** Build app from head and args array starting at offset. */
    public static Expr mkApps(Expr head, Expr[] args, int from) {
        Expr result = head;
        for (int i = from; i < args.length; i++) result = Expr.app(result, args[i]);
        return result;
    }

    // ============================================================
    // Fuel management
    // ============================================================

    private void checkFuel() {
        if (initialFuel > 0 && --fuel < 0) {
            throw new RuntimeException("WHNF reduction fuel exhausted");
        }
        if ((fuel & 0xFFF) == 0 && Thread.interrupted()) {
            throw new RuntimeException("Type checking interrupted (timeout)");
        }
    }

    /** Public fuel check for TypeChecker's isDefEq recursion. */
    public void checkFuelPublic() { checkFuel(); }

    /** Record an operation in the ring buffer trace. */
    private void traceOp(String op, Object detail) {
        traceRing[traceRingPos] = traceSeq + ":" + op + ":" + detail;
        traceRingPos = (traceRingPos + 1) & (TRACE_RING_SIZE - 1);
        traceSeq++;
    }

    /**
     * Get instrumentation counters as a HashMap (for Clojure interop).
     * Keys: "beta", "delta", "iota", "zeta", "mdata", "fvar-let", "proj",
     *        "whnf-calls", "whnf-core-cache-hits", "whnf-cache-hits", "fuel-used"
     */
    public HashMap<String, Long> getStats() {
        HashMap<String, Long> m = new HashMap<>();
        m.put("beta", betaCount);
        m.put("delta", deltaCount);
        m.put("iota", iotaCount);
        m.put("zeta", zetaCount);
        m.put("mdata", mdataCount);
        m.put("fvar-let", fvarLetCount);
        m.put("proj", projCount);
        m.put("whnf-calls", whnfCalls);
        m.put("whnf-core-cache-hits", whnfCoreCacheHits);
        m.put("whnf-cache-hits", whnfCacheHits);
        m.put("intern-hits", internHits);
        m.put("fuel-used", initialFuel - fuel);
        m.put("whnf-max-depth", (long) whnfMaxDepth);
        return m;
    }

    /** Get the expression that triggered the maximum whnf depth. */
    public Expr getMaxDepthExpr() { return whnfMaxDepthExpr; }
    /** Get the first expression at depth 100. */
    public Expr getFirstDeepExpr() { return whnfFirstDeepExpr; }
    /** Get the stack trace at depth 100. */
    public StackTraceElement[] getFirstDeepStack() { return whnfFirstDeepStack; }

    /**
     * Get the last N trace entries (most recent last).
     * Returns array of strings: "seq:op:detail".
     */
    public String[] getTraceRing() {
        int count = (int) Math.min(traceSeq, TRACE_RING_SIZE);
        String[] result = new String[count];
        int start = (traceRingPos - count + TRACE_RING_SIZE) & (TRACE_RING_SIZE - 1);
        for (int i = 0; i < count; i++) {
            result[i] = traceRing[(start + i) & (TRACE_RING_SIZE - 1)];
        }
        return result;
    }

    // ============================================================
    // Nat literal reduction
    // ============================================================

    private static final BigInteger BIG_ZERO = BigInteger.ZERO;

    private Expr natLitToConstructor(BigInteger n) {
        if (n.signum() == 0) {
            return Expr.mkConst(Name.NAT_ZERO, clojure.lang.PersistentVector.EMPTY, false);
        }
        return Expr.app(
            Expr.mkConst(Name.NAT_SUCC, clojure.lang.PersistentVector.EMPTY, false),
            Expr.litNat(n.subtract(BigInteger.ONE)));
    }

    /**
     * Reduce expression to a Nat literal, iteratively peeling Nat.succ layers.
     * Matches Lean 4's is_nat_lit_ext + get_nat_val pattern.
     *
     * Uses a two-level loop: the outer loop calls whnf once to get the initial
     * form, then an inner loop handles the common case where whnf produces
     * Nat.succ(Nat.rec...) chains by using whnfCore (iterative, no recursive whnf)
     * plus inline delta/nat reduction. This prevents deep recursive whnf chains
     * for expressions like Nat.add(604800, fvar) which would otherwise create
     * 604800 nested whnf calls.
     */
    private Expr whnfToNat(Expr e) {
        BigInteger acc = BIG_ZERO;
        Expr cur = e;
        while (true) {
            Expr w = whnf(cur);
            if (w.tag == Expr.LIT_NAT) {
                return Expr.litNat(((BigInteger) w.o0).add(acc));
            }
            if (w.tag == Expr.CONST && w.o0 == Name.NAT_ZERO) {
                return Expr.litNat(acc);
            }
            if (w.tag == Expr.APP) {
                Expr fn = (Expr) w.o0;
                if (fn.tag == Expr.CONST && fn.o0 == Name.NAT_SUCC) {
                    acc = acc.add(BigInteger.ONE);
                    // Instead of calling whnf(arg) recursively, try iterative reduction
                    Expr inner = (Expr) w.o1;
                    // Fast path: try iterative Nat reduction without recursive whnf
                    Expr iterResult = iterativeWhnfToNat(inner);
                    if (iterResult != null) {
                        return Expr.litNat(((BigInteger) iterResult.o0).add(acc));
                    }
                    // Slow path: fall back to recursive whnf
                    cur = inner;
                    continue;
                }
            }
            return null; // not reducible to Nat literal
        }
    }

    /**
     * Try to reduce a Nat expression to a literal using only iterative operations:
     * whnfCore (iterative) + cheap native Nat/Int reduction + delta unfolding.
     * No recursive whnf calls. Returns a LIT_NAT or null.
     *
     * This handles the common case of Nat.rec-based functions (like Nat.add,
     * Nat.gcd implemented via brecOn) applied to large concrete values.
     */
    private Expr iterativeWhnfToNat(Expr e) {
        BigInteger innerAcc = BIG_ZERO;
        Expr cur = e;
        for (int i = 0; i < 100_000_000; i++) { // safety limit
            checkFuel();
            // Step 1: whnfCore (iterative — handles beta, iota, proj)
            Expr w = whnfCore(cur);

            // Check result
            if (w.tag == Expr.LIT_NAT) {
                return Expr.litNat(((BigInteger) w.o0).add(innerAcc));
            }
            if (w.tag == Expr.CONST && w.o0 == Name.NAT_ZERO) {
                return Expr.litNat(innerAcc);
            }

            // Peel Nat.succ layers
            if (w.tag == Expr.APP) {
                Expr fn = (Expr) w.o0;
                if (fn.tag == Expr.CONST && fn.o0 == Name.NAT_SUCC) {
                    innerAcc = innerAcc.add(BigInteger.ONE);
                    cur = (Expr) w.o1;
                    continue;
                }
            }

            // Step 2: Try cheap native Nat/Int reduction
            Object[] fnArgs = getAppFnArgs(w);
            Expr head = (Expr) fnArgs[0];
            Expr[] args = (Expr[]) fnArgs[1];

            Expr natR = tryCheapReduceNat(head, args);
            if (natR != null) { cur = natR; continue; }
            Expr intR = tryCheapReduceInt(head, args);
            if (intR != null) { cur = intR; continue; }

            // Step 3: Try delta unfolding
            if (head.tag == Expr.CONST) {
                Expr unfolded = tryUnfoldDef(head);
                if (unfolded != null) {
                    deltaCount++;
                    cur = whnfCore(mkApps(unfolded, args));
                    continue;
                }
            }

            // Can't reduce further iteratively — return null to trigger slow path
            return null;
        }
        return null; // safety limit reached
    }

    /**
     * Construct Decidable.isTrue(@Eq.refl Nat n) for native Nat.decEq when n == m.
     * Sound by proof irrelevance: any proof of (n = n) is valid, and Eq.refl is canonical.
     */
    private static Expr mkNatDecEqTrue(Expr litN) {
        // @Eq.{1} Nat n n
        Expr eqType = Expr.app(Expr.app(
            Expr.app(Expr.mkConst(Name.EQ, new Object[]{Level.succ(Level.ZERO_LEVEL)}, false),
                     Expr.mkConst(Name.NAT, clojure.lang.PersistentVector.EMPTY, false)),
            litN), litN);
        // @Eq.refl.{1} Nat n
        Expr proof = Expr.app(
            Expr.app(Expr.mkConst(Name.EQ_REFL, new Object[]{Level.succ(Level.ZERO_LEVEL)}, false),
                     Expr.mkConst(Name.NAT, clojure.lang.PersistentVector.EMPTY, false)),
            litN);
        // @Decidable.isTrue (n = n) proof
        return Expr.app(
            Expr.app(Expr.mkConst(Name.DECIDABLE_IS_TRUE, clojure.lang.PersistentVector.EMPTY, false),
                     eqType),
            proof);
    }

    /**
     * Try native reduction of Nat.decEq / instDecidableEqNat.
     * When both args are equal Nat literals, returns Decidable.isTrue(Eq.refl n).
     * When unequal, returns null (falls through to normal evaluation).
     * Sound: proof irrelevance makes any proof of (n = n) equivalent.
     */
    private Expr tryReduceNatDecEq(Expr[] args) {
        if (args.length != 2) return null;
        Expr a = whnfToNat(args[0]);
        if (a == null) return null;
        Expr b = whnfToNat(args[1]);
        if (b == null) return null;
        if (((BigInteger) a.o0).equals((BigInteger) b.o0)) {
            return mkNatDecEqTrue(a);
        }
        return null; // unequal — let normal processing handle isFalse case
    }

    /** Cheap version: only when args are already Nat literals. */
    private static Expr tryCheapReduceNatDecEq(Expr[] args) {
        if (args.length != 2) return null;
        if (args[0].tag != Expr.LIT_NAT || args[1].tag != Expr.LIT_NAT) return null;
        if (((BigInteger) args[0].o0).equals((BigInteger) args[1].o0)) {
            return mkNatDecEqTrue(args[0]);
        }
        return null;
    }

    /**
     * Cheap version of tryReduceNat: only fires when args are ALREADY Nat literals.
     * No whnf/whnfToNat calls — avoids deep recursive chains in whnfCoreImpl.
     * Used inside whnfCoreImpl to catch operations before they unfold to Nat.rec.
     */
    private Expr tryCheapReduceNat(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST) return null;
        Name opName = (Name) head.o0;
        // Nat.decEq / instDecidableEqNat — cheap version
        if (opName == Name.NAT_DEC_EQ || opName == Name.INST_DECIDABLE_EQ_NAT) {
            return tryCheapReduceNatDecEq(args);
        }
        if (args.length == 1 && opName == Name.NAT_SUCC) {
            if (args[0].tag == Expr.LIT_NAT)
                return Expr.litNat(((BigInteger) args[0].o0).add(BigInteger.ONE));
            return null;
        }
        if (args.length != 2) return null;
        if (opName != Name.NAT_ADD && opName != Name.NAT_SUB && opName != Name.NAT_MUL &&
            opName != Name.NAT_DIV && opName != Name.NAT_MOD && opName != Name.NAT_POW &&
            opName != Name.NAT_GCD && opName != Name.NAT_BEQ && opName != Name.NAT_BLE &&
            opName != Name.NAT_LAND && opName != Name.NAT_LOR && opName != Name.NAT_XOR &&
            opName != Name.NAT_SHIFT_LEFT && opName != Name.NAT_SHIFT_RIGHT)
            return null;
        if (args[0].tag != Expr.LIT_NAT || args[1].tag != Expr.LIT_NAT) return null;
        return reduceNatBinop(opName, (BigInteger) args[0].o0, (BigInteger) args[1].o0);
    }

    /**
     * Cheap version of tryReduceInt: only fires when args are ALREADY Int literals
     * (Int.ofNat LIT_NAT or Int.negSucc LIT_NAT). No whnf calls.
     */
    private Expr tryCheapReduceInt(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST) return null;
        Name opName = (Name) head.o0;
        if (args.length == 1) {
            BigInteger a = cheapGetInt(args[0]);
            if (a == null) return null;
            if (opName == Name.INT_NEG) return mkIntLit(a.negate());
            if (opName == Name.INT_NAT_ABS) return Expr.litNat(a.abs());
            return null;
        }
        if (args.length != 2) return null;
        if (opName != Name.INT_ADD && opName != Name.INT_SUB && opName != Name.INT_MUL &&
            opName != Name.INT_EDIV && opName != Name.INT_EMOD) return null;
        BigInteger a = cheapGetInt(args[0]);
        if (a == null) return null;
        BigInteger b = cheapGetInt(args[1]);
        if (b == null) return null;
        if (opName == Name.INT_ADD) return mkIntLit(a.add(b));
        if (opName == Name.INT_SUB) return mkIntLit(a.subtract(b));
        if (opName == Name.INT_MUL) return mkIntLit(a.multiply(b));
        if (opName == Name.INT_EDIV) {
            if (b.signum() == 0) return mkIntLit(BIG_ZERO);
            BigInteger[] qr = a.divideAndRemainder(b);
            BigInteger q = qr[0], r = qr[1];
            if (r.signum() < 0) q = b.signum() > 0 ? q.subtract(BigInteger.ONE) : q.add(BigInteger.ONE);
            return mkIntLit(q);
        }
        if (opName == Name.INT_EMOD) {
            if (b.signum() == 0) return mkIntLit(a);
            return mkIntLit(a.mod(b.abs()));
        }
        return null;
    }

    /** Extract Int value from expression WITHOUT whnf — only handles direct literals. */
    private static BigInteger cheapGetInt(Expr e) {
        if (e.tag == Expr.LIT_NAT) return (BigInteger) e.o0;
        if (e.tag != Expr.APP) return null;
        Expr fn = (Expr) e.o0;
        if (fn.tag != Expr.CONST) return null;
        Expr arg = (Expr) e.o1;
        if (arg.tag != Expr.LIT_NAT) return null;
        Name name = (Name) fn.o0;
        if (name == Name.INT_OF_NAT) return (BigInteger) arg.o0;
        if (name == Name.INT_NEG_SUCC) return ((BigInteger) arg.o0).add(BigInteger.ONE).negate();
        return null;
    }

    private Expr tryReduceNat(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST) return null;
        Name opName = (Name) head.o0;

        // Nat.decEq / instDecidableEqNat — native to avoid O(n) proof recursion
        if (opName == Name.NAT_DEC_EQ || opName == Name.INST_DECIDABLE_EQ_NAT) {
            return tryReduceNatDecEq(args);
        }

        // 1-arg: Nat.succ (matching Lean 4's reduce_nat lines 647-654)
        if (args.length == 1 && opName == Name.NAT_SUCC) {
            Expr a = whnfToNat(args[0]);
            if (a == null) return null;
            return Expr.litNat(((BigInteger) a.o0).add(BigInteger.ONE));
        }

        if (args.length != 2) return null;
        // Quick identity check against interned names
        if (opName != Name.NAT_ADD && opName != Name.NAT_SUB && opName != Name.NAT_MUL &&
            opName != Name.NAT_DIV && opName != Name.NAT_MOD && opName != Name.NAT_POW &&
            opName != Name.NAT_GCD && opName != Name.NAT_BEQ && opName != Name.NAT_BLE &&
            opName != Name.NAT_LAND && opName != Name.NAT_LOR && opName != Name.NAT_XOR &&
            opName != Name.NAT_SHIFT_LEFT && opName != Name.NAT_SHIFT_RIGHT) {
            return null;
        }
        Expr a = whnfToNat(args[0]);
        Expr b = whnfToNat(args[1]);
        if (a == null || b == null) return null;
        BigInteger va = (BigInteger) a.o0;
        BigInteger vb = (BigInteger) b.o0;
        return reduceNatBinop(opName, va, vb);
    }

    private static Expr reduceNatBinop(Name op, BigInteger a, BigInteger b) {
        if (op == Name.NAT_ADD) return Expr.litNat(a.add(b));
        if (op == Name.NAT_SUB) return Expr.litNat(a.subtract(b).max(BIG_ZERO));
        if (op == Name.NAT_MUL) return Expr.litNat(a.multiply(b));
        if (op == Name.NAT_DIV) return Expr.litNat(b.signum() == 0 ? BIG_ZERO : a.divide(b));
        if (op == Name.NAT_MOD) return Expr.litNat(b.signum() == 0 ? a : a.mod(b));
        if (op == Name.NAT_POW) return Expr.litNat(a.pow(b.intValue()));
        if (op == Name.NAT_GCD) return Expr.litNat(a.gcd(b));
        if (op == Name.NAT_BEQ) return a.equals(b) ? mkBoolTrue() : mkBoolFalse();
        if (op == Name.NAT_BLE) return a.compareTo(b) <= 0 ? mkBoolTrue() : mkBoolFalse();
        if (op == Name.NAT_LAND) return Expr.litNat(a.and(b));
        if (op == Name.NAT_LOR) return Expr.litNat(a.or(b));
        if (op == Name.NAT_XOR) return Expr.litNat(a.xor(b));
        if (op == Name.NAT_SHIFT_LEFT) return Expr.litNat(a.shiftLeft(b.intValue()));
        if (op == Name.NAT_SHIFT_RIGHT) return Expr.litNat(a.shiftRight(b.intValue()));
        return null;
    }

    private static Expr mkBoolTrue() {
        return Expr.mkConst(Name.BOOL_TRUE, clojure.lang.PersistentVector.EMPTY, false);
    }

    private static Expr mkBoolFalse() {
        return Expr.mkConst(Name.BOOL_FALSE, clojure.lang.PersistentVector.EMPTY, false);
    }

    // ============================================================
    // Native Int reduction (optimization — Lean 4 reduces through defs)
    // ============================================================

    /** Try to whnf an expression to an Int constructor (ofNat or negSucc) with a Nat literal.
     *  Returns [sign, value] where sign=1 for ofNat, sign=-1 for negSucc, or null. */
    private BigInteger whnfToInt(Expr e) {
        Expr w = whnf(e);
        // Check: is it Int.ofNat(LIT_NAT) or Int.negSucc(LIT_NAT)?
        if (w.tag == Expr.APP) {
            Expr fn = (Expr) w.o0;
            if (fn.tag == Expr.CONST) {
                Name name = (Name) fn.o0;
                Expr arg = (Expr) w.o1;
                if (name == Name.INT_OF_NAT) {
                    Expr nat = whnfToNat(arg);
                    if (nat != null) return (BigInteger) nat.o0;
                } else if (name == Name.INT_NEG_SUCC) {
                    Expr nat = whnfToNat(arg);
                    if (nat != null) return ((BigInteger) nat.o0).add(BigInteger.ONE).negate();
                }
            }
        }
        // Also check: bare LIT_NAT (sometimes Int.ofNat is reduced away)
        if (w.tag == Expr.LIT_NAT) return (BigInteger) w.o0;
        return null;
    }

    /** Construct Int.ofNat(n) or Int.negSucc(n) from a BigInteger. */
    private static Expr mkIntLit(BigInteger v) {
        if (v.signum() >= 0) {
            return Expr.app(Expr.mkConst(Name.INT_OF_NAT, clojure.lang.PersistentVector.EMPTY, false),
                           Expr.litNat(v));
        } else {
            // negSucc(n) represents -(n+1), so for value v < 0: n = |v| - 1
            return Expr.app(Expr.mkConst(Name.INT_NEG_SUCC, clojure.lang.PersistentVector.EMPTY, false),
                           Expr.litNat(v.negate().subtract(BigInteger.ONE)));
        }
    }

    /**
     * Try to reduce an Int operation natively.
     * This is an optimization: Lean 4 reduces Int ops through definition unfolding to Nat,
     * but that's 1000x faster in C++. We short-circuit the chain for common operations.
     */
    Expr tryReduceInt(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST) return null;
        Name opName = (Name) head.o0;

        // Unary operations (1 arg)
        if (args.length == 1) {
            if (opName == Name.INT_NEG) {
                BigInteger a = whnfToInt(args[0]);
                if (a == null) return null;
                return mkIntLit(a.negate());
            }
            if (opName == Name.INT_NAT_ABS) {
                BigInteger a = whnfToInt(args[0]);
                if (a == null) return null;
                return Expr.litNat(a.abs());
            }
            return null;
        }

        // Binary operations (2 args)
        if (args.length != 2) return null;
        if (opName != Name.INT_ADD && opName != Name.INT_SUB && opName != Name.INT_MUL &&
            opName != Name.INT_EDIV && opName != Name.INT_EMOD) {
            return null;
        }

        BigInteger a = whnfToInt(args[0]);
        if (a == null) return null;
        BigInteger b = whnfToInt(args[1]);
        if (b == null) return null;

        if (opName == Name.INT_ADD) return mkIntLit(a.add(b));
        if (opName == Name.INT_SUB) return mkIntLit(a.subtract(b));
        if (opName == Name.INT_MUL) return mkIntLit(a.multiply(b));
        if (opName == Name.INT_EDIV) {
            if (b.signum() == 0) return mkIntLit(BIG_ZERO);
            // Euclidean division: result has sign of divisor, remainder non-negative
            BigInteger[] qr = a.divideAndRemainder(b);
            BigInteger q = qr[0], r = qr[1];
            if (r.signum() < 0) q = b.signum() > 0 ? q.subtract(BigInteger.ONE) : q.add(BigInteger.ONE);
            return mkIntLit(q);
        }
        if (opName == Name.INT_EMOD) {
            if (b.signum() == 0) return mkIntLit(a);
            BigInteger r = a.mod(b.abs());
            return mkIntLit(r);
        }
        return null;
    }

    /**
     * Try to reduce a nat operation expression to a literal.
     * Used by TypeChecker in the lazy delta loop (matching Lean 4's reduce_nat in lazy_delta_reduction).
     * Returns the reduced expression or null if not a nat op.
     */
    public Expr tryReduceNatExpr(Expr e) {
        Object[] fnArgs = getAppFnArgs(e);
        Expr head = (Expr) fnArgs[0];
        Expr[] args = (Expr[]) fnArgs[1];
        return tryReduceNat(head, args);
    }

    // ============================================================
    // Iota reduction (recursor application)
    // ============================================================

    private Expr tryReduceRecursor(Expr head, Expr[] args, boolean useWhnf) {
        if (head.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || !ci.isRecursor()) return null;

        int numParams = ci.numParams, numMotives = ci.numMotives;
        int numMinors = ci.numMinors, numIndices = ci.numIndices;
        int expectedArgs = numParams + numMotives + numMinors + numIndices + 1;
        if (args.length < expectedArgs) return null;

        int majorIdx = numParams + numMotives + numMinors + numIndices;
        Expr rawMajor = args[majorIdx];

        // Short-circuit: if major is already a constructor (Nat.succ(LIT_NAT),
        // Nat.zero, other constructor apps) skip the whnf call.
        // Also: for Nat literals, try natLitToConstructor without whnf.
        // This avoids deep whnf recursion for Nat.brecOn chains where each step
        // produces Nat.succ(LIT_NAT) as the major premise.
        Expr major;
        if (rawMajor.tag == Expr.LIT_NAT || rawMajor.tag == Expr.LIT_STR) {
            major = rawMajor;
        } else if (isConstructorApp(rawMajor)) {
            major = rawMajor;
        } else {
            major = useWhnf ? whnf(rawMajor) : rawMajor;
        }

        // Get constructor head
        Object[] fnArgs = getAppFnArgs(major);
        Expr ctorHead = (Expr) fnArgs[0];
        Expr[] ctorArgs = (Expr[]) fnArgs[1];

        // Handle nat literals (Lean 4's nat_lit_to_constructor)
        if (major.tag == Expr.LIT_NAT) {
            Expr expanded = natLitToConstructor((BigInteger) major.o0);
            ctorHead = getAppFn(expanded);
            fnArgs = getAppFnArgs(expanded);
            ctorArgs = (Expr[]) fnArgs[1];
            major = expanded;
        }

        // Handle string literals (Lean 4's string_lit_to_constructor)
        if (major.tag == Expr.LIT_STR) {
            major = whnf(stringLitToConstructor(major));
            fnArgs = getAppFnArgs(major);
            ctorHead = (Expr) fnArgs[0];
            ctorArgs = (Expr[]) fnArgs[1];
        }

        // Eta-expand structures (Lean 4's to_cnstr_when_structure in inductive.h:63-73)
        // When major premise has structure type but isn't a constructor,
        // expand it to Ctor(proj(0,e), proj(1,e), ..., proj(n-1,e)).
        // This is critical for e.g. ByteArray.push where the major premise is a fvar,
        // but also fires when the major whnf's to another recursor application.
        if (inferFn != null && ci.all != null && ci.all.length > 0 && !isConstructorApp(major)) {
            Name majorInductName = (Name) ci.all[0];
            if (isStructureLike(majorInductName)) {
                try {
                    Expr majorType = whnf(inferFn.infer(args[majorIdx]));
                    Expr typeHead = getAppFn(majorType);
                    if (typeHead.tag == Expr.CONST && typeHead.o0.equals(majorInductName)) {
                        // Check it's not a Prop (Lean 4 line 70-71)
                        Expr typeOfType = whnf(inferFn.infer(majorType));
                        if (!(typeOfType.tag == Expr.SORT && Level.simplify((Level) typeOfType.o0).tag == Level.ZERO)) {
                            // Expand: Ctor(params, proj(I, 0, e), ..., proj(I, n-1, e))
                            major = expandEtaStruct(majorInductName, majorType, args[majorIdx]);
                            fnArgs = getAppFnArgs(major);
                            ctorHead = (Expr) fnArgs[0];
                            ctorArgs = (Expr[]) fnArgs[1];
                        }
                    }
                } catch (Exception ignored) {}
            }
        }

        // Try direct rule match
        ConstantInfo.RecursorRule directRule = null;
        if (ctorHead.tag == Expr.CONST) {
            Name cn = (Name) ctorHead.o0;
            for (ConstantInfo.RecursorRule r : ci.rules) {
                if (r.ctor == cn || r.ctor.equals(cn)) { directRule = r; break; }
            }
        }

        // K-recursor: try mk_nullary_cnstr
        if (ci.isK && directRule == null && inferFn != null && isDefEqFn != null) {
            try {
                Expr majorType = whnf(inferFn.infer(args[majorIdx]));
                Expr newCnstr = mkNullaryCnstr(majorType, numParams);
                if (newCnstr != null) {
                    Expr newType = inferFn.infer(newCnstr);
                    if (isDefEqFn.isDefEq(majorType, newType)) {
                        Object[] nc = getAppFnArgs(newCnstr);
                        ctorHead = (Expr) nc[0];
                        ctorArgs = (Expr[]) nc[1];
                        major = newCnstr;
                    }
                }
            } catch (Exception ignored) {}
        }

        if (ctorHead.tag != Expr.CONST) return null;
        Name ctorName = (Name) ctorHead.o0;

        // Find matching rule
        ConstantInfo.RecursorRule rule = directRule;
        if (rule == null) {
            for (ConstantInfo.RecursorRule r : ci.rules) {
                if (r.ctor == ctorName || r.ctor.equals(ctorName)) { rule = r; break; }
            }
        }
        if (rule == null) return null;

        // Instantiate RHS with level params
        HashMap<Object, Level> subst = makeLevelSubst(ci.levelParams, constLevels(head));
        Expr rhs = instantiateLevelParams(rule.rhs, subst);

        // Build result: apply rhs to params, motives, minors, constructor fields
        Expr result = rhs;
        // params
        for (int i = 0; i < numParams; i++) result = Expr.app(result, args[i]);
        // motives
        for (int i = numParams; i < numParams + numMotives; i++) result = Expr.app(result, args[i]);
        // minors
        for (int i = numParams + numMotives; i < numParams + numMotives + numMinors; i++) result = Expr.app(result, args[i]);

        // Constructor fields (skip inductive params)
        if (major.tag == Expr.LIT_NAT) {
            Expr expanded = natLitToConstructor((BigInteger) args[majorIdx].o0);
            Object[] ea = getAppFnArgs(expanded);
            Expr[] expandedArgs = (Expr[]) ea[1];
            for (Expr a : expandedArgs) result = Expr.app(result, a);
        } else {
            ConstantInfo ctorCi = env.lookup(ctorName);
            int ctorNumParams = ctorCi != null ? ctorCi.numParams : numParams;
            for (int i = ctorNumParams; i < ctorArgs.length; i++) {
                result = Expr.app(result, ctorArgs[i]);
            }
        }

        // Apply extra args
        for (int i = majorIdx + 1; i < args.length; i++) {
            result = Expr.app(result, args[i]);
        }
        return result;
    }

    private Expr mkNullaryCnstr(Expr majorType, int numParams) {
        Object[] fa = getAppFnArgs(majorType);
        Expr typeHead = (Expr) fa[0];
        Expr[] typeArgs = (Expr[]) fa[1];
        if (typeHead.tag != Expr.CONST || typeArgs.length < numParams) return null;

        Name indName = (Name) typeHead.o0;
        ConstantInfo indCi = env.lookup(indName);
        if (indCi == null || !indCi.isInduct() || indCi.ctors.length != 1) return null;

        Name ctorName = indCi.ctors[0];
        ConstantInfo ctorCi = env.lookup(ctorName);
        if (ctorCi == null || !ctorCi.isCtor() || ctorCi.numFields != 0) return null;

        Expr result = Expr.mkConst(ctorName, constLevelsObj(typeHead), typeHead.hasLevelParam());
        for (int i = 0; i < numParams; i++) {
            result = Expr.app(result, typeArgs[i]);
        }
        return result;
    }

    /**
     * Check if an inductive type is "structure-like":
     * exactly 1 constructor, 0 indices, not recursive.
     * Matching Lean 4's is_structure_like.
     */
    private boolean isStructureLike(Name inductName) {
        ConstantInfo ci = env.lookup(inductName);
        return ci != null && ci.isInduct() &&
               ci.ctors != null && ci.ctors.length == 1 &&
               ci.numIndices == 0 && !ci.isRec;
    }

    /** Check if expression is a constructor application. */
    private boolean isConstructorApp(Expr e) {
        Expr fn = getAppFn(e);
        if (fn.tag != Expr.CONST) return false;
        ConstantInfo ci = env.lookup((Name) fn.o0);
        return ci != null && ci.isCtor();
    }

    /**
     * Eta-expand a structure value into constructor form.
     * Matching Lean 4's expand_eta_struct (inductive.cpp:98-111).
     * Given e : I params, produces I.mk(params, proj(I, 0, e), ..., proj(I, n-1, e)).
     */
    private Expr expandEtaStruct(Name inductName, Expr eType, Expr e) {
        Object[] typeFA = getAppFnArgs(eType);
        Expr typeHead = (Expr) typeFA[0];
        Expr[] typeArgs = (Expr[]) typeFA[1];

        ConstantInfo indCi = env.lookup(inductName);
        if (indCi == null || !indCi.isInduct() || indCi.ctors.length == 0) return e;

        Name ctorName = indCi.ctors[0];
        ConstantInfo ctorCi = env.lookup(ctorName);
        if (ctorCi == null) return e;

        int nparams = ctorCi.numParams;
        int nfields = ctorCi.numFields;

        // Build: Ctor(params, proj(I, 0, e), ..., proj(I, nfields-1, e))
        Expr result = Expr.mkConst(ctorName, constLevelsObj(typeHead), typeHead.hasLevelParam());
        // Apply params from the type
        for (int i = 0; i < Math.min(nparams, typeArgs.length); i++) {
            result = Expr.app(result, typeArgs[i]);
        }
        // Apply fields as projections
        for (int i = 0; i < nfields; i++) {
            result = Expr.app(result, Expr.proj(inductName, i, e));
        }
        return result;
    }

    /**
     * Convert string literal to constructor form for recursor reduction.
     * Matching Lean 4's string_lit_to_constructor (inductive.cpp:1200-1212).
     */
    private static Expr stringLitToConstructor(Expr e) {
        String str = (String) e.o0;
        Level zeroLevel = Level.ZERO_LEVEL;
        Expr charType = Expr.mkConst(Name.CHAR, new Level[0], false);
        Expr listNilChar = Expr.app(Expr.mkConst(Name.LIST_NIL, new Level[]{zeroLevel}, false), charType);
        Expr listConsChar = Expr.app(Expr.mkConst(Name.LIST_CONS, new Level[]{zeroLevel}, false), charType);
        Expr charOfNat = Expr.mkConst(Name.CHAR_OF_NAT, new Level[0], false);
        int[] codepoints = str.codePoints().toArray();
        Expr r = listNilChar;
        for (int i = codepoints.length - 1; i >= 0; i--) {
            Expr ch = Expr.app(charOfNat, Expr.litNat(BigInteger.valueOf(codepoints[i])));
            r = Expr.app(Expr.app(listConsChar, ch), r);
        }
        return Expr.app(Expr.mkConst(Name.STRING_OF_LIST, new Level[0], false), r);
    }

    // ============================================================
    // Quotient reduction
    // ============================================================

    private Expr tryReduceQuot(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST || !env.isQuotEnabled()) return null;
        Name name = (Name) head.o0;

        int mkPos, argPos;
        if (name == Name.QUOT_LIFT) {
            mkPos = 5; argPos = 3;
        } else if (name == Name.QUOT_IND) {
            mkPos = 4; argPos = 3;
        } else {
            return null;
        }

        if (args.length <= mkPos) return null;

        // Lean 4 calls whnf on the critical quotient argument before checking
        Expr mk = whnf(args[mkPos]);
        Object[] qa = getAppFnArgs(mk);
        Expr qHead = (Expr) qa[0];
        Expr[] qArgs = (Expr[]) qa[1];
        if (qHead.tag == Expr.CONST && qHead.o0 == Name.QUOT_MK && qArgs.length == 3) {
            Expr f = args[argPos], a = qArgs[2];
            Expr result = Expr.app(f, a);
            int elimArity = mkPos + 1;
            for (int i = elimArity; i < args.length; i++) result = Expr.app(result, args[i]);
            return result;
        }
        return null;
    }

    // ============================================================
    // Projection reduction
    // ============================================================

    private Expr tryReduceProj(Expr e, boolean cheapRec, boolean cheapProj) {
        if (e.tag != Expr.PROJ) return null;
        // Lean 4's reduce_proj: cheapProj → whnf_core(struct, cheapRec, cheapProj), else whnf(struct)
        Expr struct = cheapProj ? whnfCore((Expr) e.o1, cheapRec, cheapProj) : whnf((Expr) e.o1);

        // Handle string literals: proj(String, 0, lit-str) → expand to String.mk(charList)
        if (struct.tag == Expr.LIT_STR) {
            struct = whnf(stringLitToConstructor(struct));
        }

        Object[] fa = getAppFnArgs(struct);
        Expr head = (Expr) fa[0];
        Expr[] structArgs = (Expr[]) fa[1];
        if (head.tag != Expr.CONST) return null;

        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || !ci.isCtor()) return null;

        int fieldStart = ci.numParams;
        int fieldIdx = fieldStart + (int) e.longVal;
        if (fieldIdx < structArgs.length) {
            return structArgs[fieldIdx];
        }
        return null;
    }

    // ============================================================
    // Delta reduction (definition unfolding)
    // ============================================================

    Expr tryUnfoldDef(Expr head) {
        if (head.tag != Expr.CONST) return null;
        Name name = (Name) head.o0;
        ConstantInfo ci = env.lookup(name);
        if (ci == null) return null;
        Expr value = ci.getValue();
        if (value == null) return null;

        // Transparency check: in reducible mode (0), only unfold allowed names
        if (transparencyMode == 0) {
            if (deltaAllowSet == null || !deltaAllowSet.contains(name)) {
                return null;  // Not allowed to unfold this definition
            }
        }

        // Validate level param count (Lean Kernel Arena: constlevels.ndjson)
        Object[] headLevels = constLevels(head);
        if (ci.levelParams.length != headLevels.length) {
            return null;  // Wrong number of level params — refuse to unfold
        }

        // Check unfold cache
        Expr cached = unfoldCache.get(head);
        if (cached != null) return cached;

        HashMap<Object, Level> subst = makeLevelSubst(ci.levelParams, headLevels);
        // Deep re-intern: definition values from ENV were created before enableIntern().
        // Without this, their non-interned sub-expressions pollute all expression trees,
        // breaking IdentityHashMap-based caches (inferCache, eqvManager, whnfCache).
        Expr result = Expr.deepReIntern(internResult(instantiateLevelParams(value, subst)));
        unfoldCache.put(head, result);
        return result;
    }

    // ============================================================
    // WHNF core (no delta)
    // ============================================================

    /**
     * Reduce to WHNF without delta unfolding.
     * Handles: beta, zeta, iota, projection, mdata, fvar let-unfolding.
     * Default: cheapRec=false, cheapProj=false (matching Lean 4's whnf_core defaults).
     * cheapRec=false means recursor major premise is fully whnf-reduced.
     *
     * Wrapper caches ALL inputs → results for default flags, compensating for Java's
     * lack of hash-consing (Lean 4 uses hash-consing for expression identity, which
     * makes isDefEq's pointer-equality "quick" path work across whnf_core calls).
     */
    public Expr whnfCore(Expr e) {
        // Canonicalize input via intern table so IdentityHashMap cache hits
        // for structurally-equal but pointer-different expressions.
        // Matches Lean 4's hash-consing invariant: same structure → same pointer.
        // O(1) for already-canonical expressions (intern table fast-path).
        e = Expr.deepReIntern(e);
        Expr cached = whnfCoreCache.get(e);
        if (cached != null) { whnfCoreCacheHits++; return cached; }
        Expr raw = whnfCoreImpl(e, false, false);
        // Preserve pointer identity when nothing changed (Lean's is_eqp guarantee)
        Expr r = raw.isEqp(e) ? e : internResult(raw);
        whnfCoreCache.put(e, r);
        return r;
    }

    /**
     * Reduce to WHNF without delta unfolding, with Lean 4-style cheap flags.
     *
     * Cache is always READ for any flag combination (a more-reduced cached result
     * is always valid), but only WRITTEN for default flags (cheapRec=false, cheapProj=false).
     */
    public Expr whnfCore(Expr e, boolean cheapRec, boolean cheapProj) {
        if (!cheapRec && !cheapProj) return whnfCore(e);
        Expr cached = whnfCoreCache.get(e);
        if (cached != null) { whnfCoreCacheHits++; return cached; }
        return whnfCoreImpl(e, cheapRec, cheapProj);
    }

    /**
     * Iterative whnfCore implementation (type_checker.cpp:435-517).
     * Uses local args array instead of getAppFnArgs to avoid ArrayList + Object[2] allocation.
     * Nat.succ folding removed (handled by whnfLoop/reduce_nat instead).
     */
    private Expr whnfCoreImpl(Expr e, boolean cheapRec, boolean cheapProj) {
        while (true) {
            // Check cache on each iteration for cheap-flag calls, matching Lean 4's recursive
            // whnf_core which checks cache on every call (type_checker.cpp:457-459).
            if (cheapRec || cheapProj) {
                Expr cached = whnfCoreCache.get(e);
                if (cached != null) { whnfCoreCacheHits++; return cached; }
            }
            switch (e.tag) {
                case Expr.BVAR: case Expr.SORT: case Expr.LAM: case Expr.FORALL:
                case Expr.LIT_NAT: case Expr.LIT_STR:
                    return e;

                case Expr.FVAR: {
                    if (lctx != null) {
                        Object[] decl = lctx.get(e.longVal);
                        if (decl != null && ((Integer) decl[0]) == 1) { // let-decl
                            checkFuel();
                            fvarLetCount++;
                            traceOp("fvar-let", e.longVal);
                            e = (Expr) decl[3]; // value
                            continue;
                        }
                    }
                    return e;
                }

                case Expr.CONST:
                    return e;

                case Expr.MDATA:
                    checkFuel();
                    mdataCount++;
                    e = (Expr) e.o1;
                    continue;

                case Expr.LET:
                    checkFuel();
                    zetaCount++;
                    traceOp("zeta", "let");
                    e = Expr.deepReIntern(instantiate1((Expr) e.o3, (Expr) e.o2));
                    { Expr cached = whnfCoreCache.get(e); if (cached != null) { whnfCoreCacheHits++; return cached; } }
                    continue;

                case Expr.PROJ: {
                    Expr r = tryReduceProj(e, cheapRec, cheapProj);
                    if (r != null) { checkFuel(); projCount++; traceOp("proj", e.o0); e = r; continue; }
                    return e;
                }

                case Expr.APP: {
                    // Collect args in forward order using local array
                    // (avoids ArrayList + Object[2] allocation from getAppFnArgs)
                    int numArgs = 0;
                    Expr cur = e;
                    while (cur.tag == Expr.APP) { numArgs++; cur = (Expr) cur.o0; }
                    Expr f0 = cur;
                    Expr[] args = new Expr[numArgs];
                    cur = e;
                    for (int i = numArgs - 1; i >= 0; i--) {
                        args[i] = (Expr) cur.o1;
                        cur = (Expr) cur.o0;
                    }
                    Expr head2 = whnfCoreImpl(f0, cheapRec, cheapProj);
                    // Cache the head result for default flags
                    if (!cheapRec && !cheapProj && head2 != f0) {
                        head2 = internResult(head2);
                        whnfCoreCache.put(f0, head2);
                    }

                    if (head2.tag == Expr.LAM) {
                        checkFuel();
                        betaCount++;
                        traceOp("beta", numArgs);
                        Expr f = head2;
                        int m = 1;
                        while (((Expr) f.o2).tag == Expr.LAM && m < numArgs) {
                            f = (Expr) f.o2;
                            m++;
                        }
                        Expr body = instantiateRev((Expr) f.o2, m, args, 0);
                        e = Expr.deepReIntern(mkApps(body, args, m));
                        { Expr cached = whnfCoreCache.get(e); if (cached != null) { whnfCoreCacheHits++; return cached; } }
                        continue;
                    } else if (head2 == f0) {
                        // Head unchanged — try cheap native reduction BEFORE recursor.
                        // Unlike whnfLoop's tryReduceNat/tryReduceInt (which call whnfToNat/
                        // whnfToInt → whnf recursively), this only fires when args are
                        // ALREADY literals. This prevents deep recursive chains for
                        // expressions like Nat.add(UInt64.size, fvar) while still catching
                        // operations like Nat.gcd(lit, lit) before they unfold to Nat.rec.
                        Expr cheapNat = tryCheapReduceNat(f0, args);
                        if (cheapNat != null) { checkFuel(); e = cheapNat; continue; }
                        Expr cheapInt = tryCheapReduceInt(f0, args);
                        if (cheapInt != null) { checkFuel(); e = cheapInt; continue; }
                        Expr reduced = tryReduceRecursor(f0, args, !cheapRec);
                        if (reduced == null) reduced = tryReduceQuot(f0, args);
                        if (reduced != null) {
                            checkFuel();
                            iotaCount++;
                            traceOp("iota", f0.o0);
                            e = Expr.deepReIntern(reduced);
                            { Expr cached = whnfCoreCache.get(e); if (cached != null) { whnfCoreCacheHits++; return cached; } }
                            continue;
                        }
                        return e;
                    } else {
                        // Head changed but not lambda — rebuild app and continue
                        checkFuel();
                        e = Expr.deepReIntern(mkApps(head2, args));
                        { Expr cached = whnfCoreCache.get(e); if (cached != null) { whnfCoreCacheHits++; return cached; } }
                        continue;
                    }
                }

                default: return e;
            }
        }
    }

    // ============================================================
    // WHNF (full, with delta)
    // ============================================================

    /**
     * Reduce expression to weak head normal form with delta unfolding.
     */
    public Expr whnf(Expr e) {
        whnfCalls++;
        // Quick exits (matching Lean 4: no cache needed for these)
        switch (e.tag) {
            case Expr.BVAR: case Expr.SORT: case Expr.LAM: case Expr.FORALL:
            case Expr.LIT_NAT: case Expr.LIT_STR:
                return e;
        }

        // Canonicalize input so IdentityHashMap cache hits for structurally-equal inputs.
        // Matches Lean 4's global hash-consing. O(1) for already-canonical expressions.
        e = Expr.deepReIntern(e);

        // Check cache — unconditionally, matching Lean 4 (no hasFVar guard).
        // Within a single declaration check, lctx only grows monotonically,
        // so cached results for fvar-containing expressions remain valid.
        Expr cached = whnfCache.get(e);
        if (cached != null) { whnfCacheHits++; return cached; }

        whnfDepth++;
        if (whnfDepth > whnfMaxDepth) {
            whnfMaxDepth = whnfDepth;
            whnfMaxDepthExpr = e;
        }
        // Capture the expression and stack that first enters deep recursion
        if (whnfDepth == 100 && whnfFirstDeepExpr == null) {
            whnfFirstDeepExpr = e;
            whnfFirstDeepStack = Thread.currentThread().getStackTrace();
        }
        // Depth tracking is for diagnostics only — no limit enforced.
        try {
            Expr raw = whnfLoop(e);
            // Deep re-intern: ensures sub-expressions from ENV (created before
            // enableIntern) are canonicalized. Fast for already-interned expressions
            // (table.get() hit returns immediately).
            Expr result = raw.isEqp(e) ? e : Expr.deepReIntern(raw);
            whnfCache.put(e, result);
            return result;
        } finally {
            whnfDepth--;
        }
    }

    private Expr whnfLoop(Expr e) {
        // Matching Lean 4's whnf loop (type_checker.cpp lines 666-682):
        // whnf_core → try reduce_native → try reduce_nat → try unfold_definition → loop
        // Note: NO recursor reduction here — that's handled by whnfCore.
        e = whnfCore(e);
        while (true) {
            Object[] fnArgs = getAppFnArgs(e);
            Expr head = (Expr) fnArgs[0];
            Expr[] args = (Expr[]) fnArgs[1];

            // Try nat reduction (matching Lean 4's reduce_nat in whnf)
            Expr natResult = tryReduceNat(head, args);
            if (natResult != null) {
                checkFuel();
                traceOp("nat", head.o0);
                e = whnfCore(natResult);
                continue;
            }

            // Try Int reduction (native optimization — bypasses def unfolding chain)
            Expr intResult = tryReduceInt(head, args);
            if (intResult != null) {
                checkFuel();
                e = whnfCore(intResult);
                continue;
            }

            Expr unfolded = tryUnfoldDef(head);
            if (unfolded != null) {
                checkFuel();
                deltaCount++;
                traceOp("delta", head.o0);
                e = whnfCore(mkApps(unfolded, args));
                continue;
            }

            // Nat.succ is now handled by tryReduceNat (1-arg case above)
            return e;
        }
    }

    // ============================================================
    // Helper methods
    // ============================================================

    /** Extract levels from a CONST expression as Object (could be vector or array). */
    private static Object constLevelsObj(Expr e) {
        return e.o1;
    }

    /** Extract levels from a CONST expression as a list for iteration. */
    @SuppressWarnings("unchecked")
    static Object[] constLevels(Expr e) {
        Object levels = e.o1;
        if (levels instanceof Object[]) return (Object[]) levels;
        if (levels instanceof clojure.lang.IPersistentVector) {
            clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) levels;
            Object[] arr = new Object[v.count()];
            for (int i = 0; i < arr.length; i++) arr[i] = v.nth(i);
            return arr;
        }
        if (levels instanceof java.util.List) {
            java.util.List<?> list = (java.util.List<?>) levels;
            return list.toArray();
        }
        return new Object[0];
    }

    private static HashMap<Object, Level> makeLevelSubst(Object[] paramNames, Object[] levels) {
        // Callers should validate counts match before calling.
        // Use min as safety net but this shouldn't happen with validated input.
        HashMap<Object, Level> subst = new HashMap<>(paramNames.length * 2);
        int n = Math.min(paramNames.length, levels.length);
        for (int i = 0; i < n; i++) {
            subst.put(paramNames[i], (Level) levels[i]);
        }
        return subst;
    }

    /** Clear all caches (call when starting a new declaration check). */
    public void clearCaches() {
        whnfCoreCache.clear();
        whnfCache.clear();
        unfoldCache.clear();
        resultIntern.clear();
    }
}
