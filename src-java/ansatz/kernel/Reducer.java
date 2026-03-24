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

    // Depth tracking
    private int whnfDepth;
    private static final int MAX_WHNF_DEPTH = 8192;

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
        this.whnfDepth = 0;
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
    private static final int INTERN_MAX = 100000;

    private Expr internResult(Expr r) {
        if (resultIntern.size() >= INTERN_MAX) {
            resultIntern.clear();
        }
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
                ArrayList<Expr> args = new ArrayList<>();
                Expr cur = e;
                while (cur.tag == Expr.APP && cur.hasLevelParam() && cache.get(cur) == null) {
                    args.add((Expr) cur.o1);
                    cur = (Expr) cur.o0;
                }
                Expr newHead = instantiateLPGo(cur, subst, cache);
                result = newHead;
                boolean changed = (newHead != cur);
                for (int i = args.size() - 1; i >= 0; i--) {
                    Expr origArg = args.get(i);
                    Expr newArg = instantiateLPGo(origArg, subst, cache);
                    changed = changed || (newArg != origArg);
                    result = Expr.app(result, newArg);
                }
                if (!changed) result = e;
                break;
            }
            case Expr.LAM: {
                Expr newType = instantiateLPGo((Expr) e.o1, subst, cache);
                Expr newBody = instantiateLPGo((Expr) e.o2, subst, cache);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.lam(e.o0, newType, newBody, e.o3);
                break;
            }
            case Expr.FORALL: {
                Expr newType = instantiateLPGo((Expr) e.o1, subst, cache);
                Expr newBody = instantiateLPGo((Expr) e.o2, subst, cache);
                result = (newType == e.o1 && newBody == e.o2) ? e : Expr.forall(e.o0, newType, newBody, e.o3);
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
    public static Object[] getAppFnArgs(Expr e) {
        if (e.tag != Expr.APP) return new Object[]{e, new Expr[0]};
        ArrayList<Expr> args = new ArrayList<>();
        while (e.tag == Expr.APP) {
            args.add((Expr) e.o1);
            e = (Expr) e.o0;
        }
        // Reverse args
        Expr[] argsArr = new Expr[args.size()];
        for (int i = 0; i < argsArr.length; i++) {
            argsArr[i] = args.get(argsArr.length - 1 - i);
        }
        return new Object[]{e, argsArr};
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
        return m;
    }

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

    private Expr whnfToNat(Expr e) {
        Expr w = whnf(e);
        if (w.tag == Expr.LIT_NAT) return w;
        if (w.tag == Expr.APP) {
            Expr fn = (Expr) w.o0;
            if (fn.tag == Expr.CONST && fn.o0 == Name.NAT_SUCC) {
                Expr inner = whnfToNat((Expr) w.o1);
                if (inner != null) {
                    return Expr.litNat(((BigInteger) inner.o0).add(BigInteger.ONE));
                }
            }
        }
        if (w.tag == Expr.CONST && w.o0 == Name.NAT_ZERO) {
            return Expr.litNat(BIG_ZERO);
        }
        return null;
    }

    private Expr tryReduceNat(Expr head, Expr[] args) {
        if (head.tag != Expr.CONST || args.length != 2) return null;
        Name opName = (Name) head.o0;
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
        Expr major = useWhnf ? whnf(args[majorIdx]) : args[majorIdx];

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
        Expr result = internResult(instantiateLevelParams(value, subst));
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
                    e = instantiate1((Expr) e.o3, (Expr) e.o2);
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
                        e = mkApps(body, args, m);
                        continue;
                    } else if (head2 == f0) {
                        // Head unchanged — try iota/quot reduction
                        Expr reduced = tryReduceRecursor(f0, args, !cheapRec);
                        if (reduced == null) reduced = tryReduceQuot(f0, args);
                        if (reduced != null) {
                            checkFuel();
                            iotaCount++;
                            traceOp("iota", f0.o0);
                            e = reduced;
                            continue;
                        }
                        return e;
                    } else {
                        // Head changed but not lambda — rebuild app and continue
                        checkFuel();
                        e = mkApps(head2, args);
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

        // Check cache — unconditionally, matching Lean 4 (no hasFVar guard).
        // Within a single declaration check, lctx only grows monotonically,
        // so cached results for fvar-containing expressions remain valid.
        Expr cached = whnfCache.get(e);
        if (cached != null) { whnfCacheHits++; return cached; }

        if (whnfDepth >= MAX_WHNF_DEPTH) {
            throw new RuntimeException("WHNF depth limit exceeded");
        }
        whnfDepth++;
        try {
            Expr raw = whnfLoop(e);
            // Preserve pointer identity when nothing changed (Lean's is_eqp guarantee)
            Expr result = raw.isEqp(e) ? e : internResult(raw);
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

            // Try delta (matching Lean 4's unfold_definition in whnf)
            Expr unfolded = tryUnfoldDef(head);
            if (unfolded != null) {
                checkFuel();
                deltaCount++;
                traceOp("delta", head.o0);
                e = whnfCore(mkApps(unfolded, args));
                continue;
            }

            // Nat.succ folding (Lean 4 handles this in reduce_nat)
            if (head.tag == Expr.CONST && head.o0 == Name.NAT_SUCC && args.length == 1) {
                Expr argWhnf = whnf(args[0]);
                if (argWhnf.tag == Expr.LIT_NAT) {
                    return Expr.litNat(((BigInteger) argWhnf.o0).add(BigInteger.ONE));
                }
            }

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
