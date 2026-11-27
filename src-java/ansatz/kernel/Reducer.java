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
    // type_checker::state (type_checker.h:33-44): expr_map<expr> m_whnf_core, m_whnf, m_unfold
    private final ExprMap<Expr> whnfCoreCache;
    private final ExprMap<Expr> whnfCache;
    private final ExprMap<Expr> unfoldCache;

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
    int whnfDepth;           // current recursion depth
    int whnfMaxDepth;        // max recursion depth seen
    Expr whnfMaxDepthExpr;   // expression at max depth

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
        policyChanged();
    }

    // The type checker's caches (inference, definitional equality) depend on the unfolding
    // policy as much as the reducer's own: every policy change clears both.
    private Runnable policyListener;
    void setPolicyListener(Runnable listener) { this.policyListener = listener; }

    private void policyChanged() {
        this.whnfCoreCache.clear();
        this.whnfCache.clear();
        this.unfoldCache.clear();
        if (policyListener != null) policyListener.run();
    }

    public int getTransparency() { return transparencyMode; }

    // When transparencyMode=0 (reducible), ONLY unfold names in this set
    private java.util.HashSet<Name> deltaAllowSet = null;

    /** Set the allow-list for reducible mode. Only these names will be delta-reduced
     *  when transparency=0. Pass null to clear. The set is copied: the caches depend on it, so
     *  a later change to the caller's set must not change it (set it again instead). */
    public void setDeltaAllowSet(java.util.HashSet<Name> names) {
        this.deltaAllowSet = names == null ? null : new java.util.HashSet<>(names);
        policyChanged();
    }

    // When transparencyMode=0 (reducible), ALSO unfold the names this predicate accepts: a
    // transparency given by a rule (Lean's reducibility status) rather than a finite list.
    private java.util.function.Predicate<Name> deltaAllowPredicate = null;

    /** Set the allow-predicate for reducible mode (transparency=0). Pass null to clear. The
     *  caches depend on its answers: it must answer the same for a name until it is set again
     *  (a predicate whose answers change must be set again, which clears the caches). */
    public void setDeltaAllowPredicate(java.util.function.Predicate<Name> pred) {
        this.deltaAllowPredicate = pred;
        policyChanged();
    }

    // Structure eta for recursor majors (to_cnstr_when_structure). Always on in the kernel;
    // meta-level callers may turn it off, as Lean's Meta.Config.etaStruct does.
    private boolean structureEta = true;

    /** Meta-level switch for structure eta on recursor majors (the kernel always uses it). */
    public void setStructureEta(boolean on) {
        this.structureEta = on;
        policyChanged();
    }

    /** May the definition `name` be delta-unfolded at the current transparency? Always outside
     *  reducible mode (0); in it, only names in the allow set or accepted by the allow predicate. */
    public boolean canUnfold(Name name) {
        if (transparencyMode != 0) return true;
        return (deltaAllowSet != null && deltaAllowSet.contains(name))
            || (deltaAllowPredicate != null && deltaAllowPredicate.test(name));
    }

    // The type checker's inference, conversion and Prop test, for K-like and structure-eta
    // reduction of recursor majors (Lean's reduce_recursor passes the same three).
    private InferFn inferFn;
    private IsDefEqFn isDefEqFn;
    private IsPropFn isPropFn;

    @FunctionalInterface
    public interface InferFn {
        Expr infer(Expr e);
    }

    @FunctionalInterface
    public interface IsDefEqFn {
        boolean isDefEq(Expr a, Expr b);
    }

    @FunctionalInterface
    public interface IsPropFn {
        boolean isProp(Expr type);
    }

    public Reducer(Env env) {
        this.env = env;
        this.whnfCoreCache = new ExprMap<>(8);
        this.whnfCache = new ExprMap<>(8);
        this.unfoldCache = new ExprMap<>(8);
        this.lctx = null;
        this.fuel = DEFAULT_FUEL;
        this.initialFuel = DEFAULT_FUEL;
    }

    /** Set fuel limit. 0 means unlimited (no fuel checking). */
    public void setFuel(long fuel) { this.fuel = fuel; this.initialFuel = fuel; }
    public long getFuelUsed() { return initialFuel > 0 ? initialFuel - fuel : -fuel; }
    /** Continue prev's budget: same limit, what it has left (an exhausted budget stays exhausted). */
    void continueFuel(Reducer prev) { this.fuel = prev.fuel; this.initialFuel = prev.initialFuel; }
    // the owning checker's local context (shared, not copied); only the checker registers locals
    void setLctx(HashMap<Long, Object[]> lctx) { this.lctx = lctx; }
    public void setCallbacks(InferFn inferFn, IsDefEqFn isDefEqFn, IsPropFn isPropFn) {
        this.inferFn = inferFn;
        this.isDefEqFn = isDefEqFn;
        this.isPropFn = isPropFn;
    }

    /** Callbacks without a Prop test: `type` is a proposition when its type is `Sort 0` up to
     *  normalization (Lean's is_prop), a stuck sort being an error. */
    public void setCallbacks(InferFn inferFn, IsDefEqFn isDefEqFn) {
        setCallbacks(inferFn, isDefEqFn, type -> {
            Expr s = whnf(inferFn.infer(type));
            if (s.tag != Expr.SORT) throw new RuntimeException("Type error: type expected, got " + s);
            return Level.normalizesToZero((Level) s.o0);
        });
    }



    // ============================================================
    // de Bruijn operations
    // ============================================================

    /**
     * Lift (shift) free de Bruijn indices in e by d, starting from cutoff c.
     */
    public static Expr lift(Expr e, int d, int c) {
        if (d == 0 || e.bvarRange() <= c) return e;
        return liftGo(e, d, c, new ArrayList<>());
    }

    private static IdentityHashMap<Expr, Expr> getDepthCache(ArrayList<IdentityHashMap<Expr, Expr>> caches, int depth) {
        while (caches.size() <= depth) caches.add(null);
        IdentityHashMap<Expr, Expr> m = caches.get(depth);
        if (m == null) {
            // Each binder depth has its own table; most start with only a few live terms.
            m = new IdentityHashMap<>(4);
            caches.set(depth, m);
        }
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

    /** Replace bvar(0) with val and shift remaining loose indices down by one. */
    public static Expr instantiate1(Expr e, Expr val) {
        if (e.bvarRange() == 0) return e;
        return instantiateRev(e, 1, new Expr[]{val}, 0);
    }

    /** Substitute in application order, as in Lean's instantiate_rev: the last
     *  argument in the slice replaces bvar(0). */
    public static Expr instantiateRev(Expr e, int n, Expr[] subst, int substOffset) {
        if (n == 0 || e.bvarRange() == 0) return e;
        return new Instantiate(subst, substOffset, n).apply(e, 0);
    }

    private static final class Instantiate {
        final Expr[] subst;
        final int start;
        final int count;
        final ArrayList<IdentityHashMap<Expr, Expr>> caches = new ArrayList<>();
        final ArrayList<Expr> spine = new ArrayList<>();

        Instantiate(Expr[] subst, int start, int count) {
            this.subst = subst;
            this.start = start;
            this.count = count;
        }

        Expr apply(Expr e, int depth) {
            if (e.bvarRange() <= depth) return e;
            IdentityHashMap<Expr, Expr> cache = getDepthCache(caches, depth);
            Expr result = cache.get(e);
            if (result != null) return result;
            switch (e.tag) {
                case Expr.BVAR: {
                    if (e.longVal < depth) return e;
                    long index = e.longVal - depth;
                    result = index < count
                        ? lift(subst[start + count - 1 - (int) index], depth, 0)
                        : Expr.bvar(e.longVal - count);
                    break;
                }
                case Expr.APP: {
                    // Nested argument visits use the stack above this frame.
                    // Prefixes are memoized like any subterm: a prefix shared elsewhere in the
                    // term is rebuilt once.
                    int base = spine.size();
                    Expr fn = e, head = null;
                    while (fn.tag == Expr.APP && fn.bvarRange() > depth) {
                        if (fn != e && (head = cache.get(fn)) != null) break;
                        spine.add(fn);
                        fn = (Expr) fn.o0;
                    }
                    result = head != null ? head : apply(fn, depth);
                    while (spine.size() > base) {
                        Expr app = spine.remove(spine.size() - 1);
                        Expr arg = apply((Expr) app.o1, depth);
                        result = result == app.o0 && arg == app.o1 ? app : Expr.app(result, arg);
                        if (app != e) cache.put(app, result);
                    }
                    break;
                }
                case Expr.LAM: case Expr.FORALL: {
                    Expr type = apply((Expr) e.o1, depth);
                    Expr body = apply((Expr) e.o2, depth + 1);
                    if (type == e.o1 && body == e.o2) result = e;
                    else if (e.tag == Expr.LAM) result = Expr.lam(e.o0, type, body, e.o3);
                    else result = Expr.forall(e.o0, type, body, e.o3);
                    break;
                }
                case Expr.LET: {
                    Expr type = apply((Expr) e.o1, depth);
                    Expr value = apply((Expr) e.o2, depth);
                    Expr body = apply((Expr) e.o3, depth + 1);
                    result = type == e.o1 && value == e.o2 && body == e.o3
                        ? e : Expr.mkLet(e.o0, type, value, body);
                    break;
                }
                case Expr.MDATA: {
                    Expr inner = apply((Expr) e.o1, depth);
                    result = inner == e.o1 ? e : Expr.mdata(e.o0, inner);
                    break;
                }
                case Expr.PROJ: {
                    Expr inner = apply((Expr) e.o1, depth);
                    result = inner == e.o1 ? e : Expr.proj(e.o0, e.longVal, inner);
                    break;
                }
                default: return e;
            }
            cache.put(e, result);
            return result;
        }
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
                    result = anyChanged ? Expr.mkConstOwned(e.o0, newLvls) : e;
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
                        result = Expr.mkConstOwned(e.o0, newLevelsObj);
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
            throw new KernelAbort("WHNF reduction fuel exhausted");
        }
        if ((fuel & 0xFFF) == 0 && Thread.interrupted()) {
            throw new KernelAbort("Type checking interrupted (timeout)");
        }
    }

    /** Public fuel check for TypeChecker's isDefEq recursion. */
    public void checkFuelPublic() { checkFuel(); }

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
        m.put("fuel-used", initialFuel - fuel);
        m.put("whnf-max-depth", (long) whnfMaxDepth);
        return m;
    }

    /** Get the expression that triggered the maximum whnf depth. */
    public Expr getMaxDepthExpr() { return whnfMaxDepthExpr; }

    // ============================================================
    // Nat literals and primitives (Lean's reduce_nat)
    // ============================================================

    private static final BigInteger BIG_ZERO = BigInteger.ZERO;
    private static final Object[] NO_LEVELS = new Object[0];
    private static final Expr NAT_ZERO_CONST = Expr.mkConstOwned(Name.NAT_ZERO, NO_LEVELS);
    private static final Expr NAT_SUCC_CONST = Expr.mkConstOwned(Name.NAT_SUCC, NO_LEVELS);

    /** `e` is the constant `n` with no universe arguments — Lean compares complete constants. */
    static boolean isConst0(Expr e, Name n) {
        return e.tag == Expr.CONST && n.equals(e.o0) && constLevels(e).length == 0;
    }

    static boolean isNatZeroConst(Expr e) { return isConst0(e, Name.NAT_ZERO); }
    static boolean isNatSuccConst(Expr e) { return isConst0(e, Name.NAT_SUCC); }

    /** Lean's nat_lit_to_constructor. */
    private static Expr natLitToConstructor(BigInteger n) {
        return n.signum() == 0 ? NAT_ZERO_CONST : Expr.app(NAT_SUCC_CONST, Expr.litNat(n.subtract(BigInteger.ONE)));
    }

    /** Lean's is_nat_lit_ext / get_nat_val: the value of `Nat.zero` or a literal, else null. */
    private static BigInteger natLitExt(Expr e) {
        if (e.tag == Expr.LIT_NAT) return (BigInteger) e.o0;
        return isNatZeroConst(e) ? BIG_ZERO : null;
    }

    /**
     * lean4#14849: the largest `Nat` numeral the kernel builds, in bytes — Lean's
     * LEAN_NAT_MAX_SIZE (default 128 MiB), read as read_nat_size_env reads it. The JVM property
     * ansatz.kernel.natMaxBytes takes precedence.
     */
    public static final long NAT_MAX_BYTES_DEFAULT = 128L * 1024 * 1024;
    public static final long NAT_MAX_BYTES = natMaxBytes();
    private static long natMaxBytes() {
        String v = System.getProperty("ansatz.kernel.natMaxBytes");
        if (v == null) v = System.getenv("LEAN_NAT_MAX_SIZE");
        return v == null ? NAT_MAX_BYTES_DEFAULT : readNatSizeSetting(v, NAT_MAX_BYTES_DEFAULT);
    }

    /**
     * Lean's read_nat_size_env: `strtoull(s, &end, 10)`, falling back to the default when no
     * digit was read or characters follow the number. Like strtoull: leading C whitespace and
     * one sign are accepted, a minus negates modulo 2^64, an out-of-range magnitude reads as
     * ULLONG_MAX. The result is an unsigned 64-bit value.
     */
    public static long readNatSizeSetting(String s, long dflt) {
        int i = 0, n = s.length();
        while (i < n && " \t\n\u000B\f\r".indexOf(s.charAt(i)) >= 0) i++;
        boolean neg = false;
        if (i < n && (s.charAt(i) == '+' || s.charAt(i) == '-')) { neg = s.charAt(i) == '-'; i++; }
        int start = i;
        long v = 0;
        boolean overflow = false;
        for (; i < n && s.charAt(i) >= '0' && s.charAt(i) <= '9'; i++) {
            int d = s.charAt(i) - '0';
            if (overflow) continue;
            if (Long.compareUnsigned(v, Long.divideUnsigned(-1L - d, 10)) > 0) overflow = true;
            else v = v * 10 + d;
        }
        if (i == start || i != n) return dflt;
        if (overflow) return -1L;   // ULLONG_MAX
        return neg ? -v : v;
    }

    /** Lean's lean_nat_size_in_bytes on a 64-bit runtime: a scalar (below 2^63) is one machine
     *  word, a big number its 64-bit limbs. */
    public static long natBytes(BigInteger n) {
        int bits = n.bitLength();
        return bits <= 63 ? 8 : ((bits + 63L) / 64) * 8;
    }

    /** Lean's check_nat_size: `numBytes` bounds the size of a numeral. */
    static void checkNatSize(long numBytes) { checkNatSize(numBytes, NAT_MAX_BYTES); }

    static void checkNatSize(long numBytes, long maxBytes) {
        if (Long.compareUnsigned(numBytes, maxBytes) > 0)
            throw new RuntimeException("the kernel refused a `Nat` numeral because its size exceeds the maximum; "
                + "increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
    }

    public static void checkNatSize(BigInteger n) { checkNatSize(natBytes(n)); }

    /** Lean's get_count_arg: the exponent / shift amount of pow / shiftLeft fits 32 unsigned bits. */
    private static long countArg(BigInteger count, String op) {
        if (count.bitLength() > 32)
            throw new RuntimeException("the kernel refused to evaluate `" + op
                + "` because its second argument does not fit in a 32-bit unsigned integer");
        return count.longValue();
    }

    /**
     * A BigInteger holds at most 2^31 - 1 bits. Lean's numerals are bounded only by
     * LEAN_NAT_MAX_SIZE; when a configured limit admits a result the JVM cannot hold, the kernel
     * refuses it (a resource error, like Lean's own size limit) rather than narrowing a count.
     */
    static final long JVM_MAX_NAT_BITS = Integer.MAX_VALUE;

    /**
     * Whether base^k (base ≥ 2, k ≥ 1) fits a BigInteger: 1 it fits, -1 it provably does not.
     * A power of two is exact ((bits(base) - 1) * k + 1 bits); otherwise the bit length
     * floor(k * log2(base)) + 1 is estimated in double precision with a two-bit margin, and a
     * result inside the margin counts as fitting — computing it then decides (BigInteger
     * multiplication refuses an overflow itself).
     */
    public static int powRepresentability(BigInteger base, long k) {
        int bl = base.bitLength();
        if (base.getLowestSetBit() == bl - 1) return (bl - 1) * (double) k + 1 <= JVM_MAX_NAT_BITS ? 1 : -1;
        int sh = Math.max(0, bl - 53);
        double log2 = sh + Math.log(base.shiftRight(sh).doubleValue()) / Math.log(2);
        return Math.floor(k * log2) + 1 - 2 <= JVM_MAX_NAT_BITS ? 1 : -1;
    }

    /** base^k for a result known to fit, by squaring and multiplying: BigInteger.pow refuses
     *  once bits(base) * k exceeds the range, which can be far above the true result size. */
    private static BigInteger exactPow(BigInteger base, long k) {
        if (base.getLowestSetBit() == base.bitLength() - 1)
            return BigInteger.ONE.shiftLeft((int) ((base.bitLength() - 1) * k));
        if ((long) base.bitLength() * k <= JVM_MAX_NAT_BITS) return base.pow((int) k);
        BigInteger r = BigInteger.ONE, b = base;
        try {
            for (long e = k; e > 0; e >>= 1) {
                if ((e & 1) != 0) r = r.multiply(b);
                if (e > 1) b = b.multiply(b);
            }
        } catch (ArithmeticException overflow) {
            throw new RuntimeException("the kernel refused to evaluate `Nat.pow` because the result cannot be "
                + "represented on this JVM (at most " + JVM_MAX_NAT_BITS + " bits)");
        }
        return r;
    }

    private static void checkRepresentable(long bits, String op) {
        if (bits < 0 || bits > JVM_MAX_NAT_BITS)
            throw new RuntimeException("the kernel refused to evaluate `" + op
                + "` because the result cannot be represented on this JVM (at most " + JVM_MAX_NAT_BITS + " bits)");
    }

    private static Expr mkBool(boolean b) {
        return Expr.mkConstOwned(b ? Name.BOOL_TRUE : Name.BOOL_FALSE, NO_LEVELS);
    }

    /**
     * Lean's reduce_nat: `Nat.succ n` and the binary primitives on literals (after whnf of the
     * operands, the left one first), matched as complete constants. Returns null otherwise.
     */
    public Expr reduceNat(Expr e) {
        if (e.tag != Expr.APP) return null;
        Expr f = (Expr) e.o0;
        if (f.tag != Expr.APP) {
            if (!isNatSuccConst(f)) return null;
            BigInteger v = natLitExt(whnf((Expr) e.o1));
            if (v == null) return null;
            checkRepresentable(v.bitLength() + 1L, "Nat.succ");
            v = v.add(BigInteger.ONE);
            checkNatSize(v);
            checkFuel();
            return Expr.litNat(v);
        }
        Expr op = (Expr) f.o0;
        if (op.tag != Expr.CONST || constLevels(op).length != 0) return null;
        Name n = (Name) op.o0;
        if (!NAT_BINOPS.contains(n)) return null;
        BigInteger a = natLitExt(whnf((Expr) f.o1));
        if (a == null) return null;
        BigInteger b = natLitExt(whnf((Expr) e.o1));
        if (b == null) return null;
        checkFuel();
        return natBinop(n, a, b);
    }

    private static final java.util.Set<Name> NAT_BINOPS = java.util.Set.of(
        Name.NAT_ADD, Name.NAT_SUB, Name.NAT_MUL, Name.NAT_DIV, Name.NAT_MOD, Name.NAT_POW, Name.NAT_GCD,
        Name.NAT_BEQ, Name.NAT_BLE, Name.NAT_LAND, Name.NAT_LOR, Name.NAT_XOR, Name.NAT_SHIFT_LEFT, Name.NAT_SHIFT_RIGHT);

    private static Expr checked(BigInteger r, long maxBytes) {
        checkNatSize(natBytes(r), maxBytes);
        return Expr.litNat(r);
    }

    static Expr natBinop(Name op, BigInteger a, BigInteger b) { return natBinop(op, a, b, NAT_MAX_BYTES); }

    /**
     * The primitive `op` on literals, under the numeral limit `maxBytes` (Lean's reduce_bin_nat_op,
     * reduce_pow, reduce_shiftLeft, reduce_bin_nat_pred). Shared with the Clojure reducer.
     */
    public static Expr natBinop(Name op, BigInteger a, BigInteger b, long maxBytes) {
        if (op == Name.NAT_ADD) {
            checkRepresentable(Math.max(a.bitLength(), b.bitLength()) + 1L, "Nat.add");
            return checked(a.add(b), maxBytes);
        }
        if (op == Name.NAT_SUB) return checked(a.subtract(b).max(BIG_ZERO), maxBytes);
        if (op == Name.NAT_MUL) {
            checkRepresentable((long) a.bitLength() + b.bitLength(), "Nat.mul");
            return checked(a.multiply(b), maxBytes);
        }
        if (op == Name.NAT_DIV) return Expr.litNat(b.signum() == 0 ? BIG_ZERO : a.divide(b));
        if (op == Name.NAT_MOD) return Expr.litNat(b.signum() == 0 ? a : a.mod(b));
        if (op == Name.NAT_GCD) return Expr.litNat(a.gcd(b));
        if (op == Name.NAT_BEQ) return mkBool(a.equals(b));
        if (op == Name.NAT_BLE) return mkBool(a.compareTo(b) <= 0);
        if (op == Name.NAT_LAND) return Expr.litNat(a.and(b));
        if (op == Name.NAT_LOR) return Expr.litNat(a.or(b));
        if (op == Name.NAT_XOR) return Expr.litNat(a.xor(b));
        if (op == Name.NAT_POW) {
            long k = countArg(b, "Nat.pow");
            // base^k has at most size(base) * k bytes; compare by division (no overflow)
            if (a.compareTo(BigInteger.ONE) > 0 && k != 0
                    && Long.compareUnsigned(natBytes(a), Long.divideUnsigned(maxBytes, k)) > 0)
                throw new RuntimeException("the kernel refused to evaluate `Nat.pow` because the result would exceed "
                    + "the maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
            if (a.compareTo(BigInteger.ONE) <= 0) return Expr.litNat(a.signum() == 0 && k != 0 ? BIG_ZERO : BigInteger.ONE);
            if (k == 0) return Expr.litNat(BigInteger.ONE);
            // the count narrows only once the result is known to fit
            if (powRepresentability(a, k) < 0) checkRepresentable(-1, "Nat.pow");
            return Expr.litNat(exactPow(a, k));
        }
        if (op == Name.NAT_SHIFT_LEFT) {
            if (a.signum() == 0) return Expr.litNat(BIG_ZERO);
            long k = countArg(b, "Nat.shiftLeft");
            checkNatSize(natBytes(a) + k / 8 + 1, maxBytes);
            checkRepresentable(a.bitLength() + k, "Nat.shiftLeft");
            return Expr.litNat(a.shiftLeft((int) k));
        }
        if (op == Name.NAT_SHIFT_RIGHT) {
            if (b.compareTo(BigInteger.valueOf(a.bitLength())) >= 0) return Expr.litNat(BIG_ZERO);
            return Expr.litNat(a.shiftRight(b.intValue()));
        }
        return null;
    }

    // ============================================================
    // Iota and quotient reduction (Lean's reduce_recursor, inductive.h, quot.h)
    // ============================================================

    /**
     * Lean's reduce_recursor: quotient reduction when the quotient is initialized, then iota.
     * Lean's is_quot_initialized is a flag; Env.isQuotEnabled checks the quotient package (on a
     * staged store view, on every call), so it is asked only for a `Quot.lift` / `Quot.ind` head —
     * the only applications quot_reduce_rec reduces.
     */
    private Expr reduceRecursor(Expr e, boolean cheapRec, boolean cheapProj) {
        Expr fn = getAppFn(e);
        if (fn.tag == Expr.CONST && (Name.QUOT_LIFT.equals(fn.o0) || Name.QUOT_IND.equals(fn.o0))
                && env.isQuotEnabled()) {
            Expr r = quotReduceRec(e);
            if (r != null) return r;
        }
        return inductiveReduceRec(e, cheapRec, cheapProj);
    }

    /** The whnf a recursor uses for its major premise (and K / structure eta): whnf_core when cheap. */
    private Expr recWhnf(Expr e, boolean cheapRec, boolean cheapProj) {
        return cheapRec ? whnfCoreImpl(e, cheapRec, cheapProj) : whnf(e);
    }

    /** Lean's inductive_reduce_rec. */
    private Expr inductiveReduceRec(Expr e, boolean cheapRec, boolean cheapProj) {
        Object[] fa = getAppFnArgs(e);
        Expr recFn = (Expr) fa[0];
        Expr[] recArgs = (Expr[]) fa[1];
        if (recFn.tag != Expr.CONST) return null;
        ConstantInfo rec = env.lookup((Name) recFn.o0);
        if (rec == null || !rec.isRecursor()) return null;
        int majorIdx = rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices;
        if (majorIdx >= recArgs.length) return null;
        Expr major = recArgs[majorIdx];
        if (rec.isK && inferFn != null) major = toCnstrWhenK(rec, major, cheapRec, cheapProj);
        major = recWhnf(major, cheapRec, cheapProj);
        if (major.tag == Expr.LIT_NAT) major = natLitToConstructor((BigInteger) major.o0);
        else if (major.tag == Expr.LIT_STR) major = recWhnf(stringLitToConstructor(major), cheapRec, cheapProj);
        else if (inferFn != null) major = toCnstrWhenStructure(getMajorInductName(rec), major, cheapRec, cheapProj);
        Expr ctor = getAppFn(major);
        if (ctor.tag != Expr.CONST) return null;
        ConstantInfo.RecursorRule rule = null;
        for (ConstantInfo.RecursorRule r : rec.rules)
            if (r.ctor.equals(ctor.o0)) { rule = r; break; }
        if (rule == null) return null;
        Expr[] majorArgs = (Expr[]) getAppFnArgs(major)[1];
        if (rule.nfields > majorArgs.length) return null;
        Object[] recLevels = constLevels(recFn);
        if (recLevels.length != rec.levelParams.length) return null;
        Expr rhs = instantiateLevelParams(rule.rhs, makeLevelSubst(rec.levelParams, recLevels));
        rhs = mkApps(rhs, java.util.Arrays.copyOf(recArgs, rec.numParams + rec.numMotives + rec.numMinors));
        // nested inductives: the constructor's parameters need not be the recursor's
        int nparams = majorArgs.length - rule.nfields;
        for (int i = nparams; i < majorArgs.length; i++) rhs = Expr.app(rhs, majorArgs[i]);
        return mkApps(rhs, recArgs, majorIdx + 1);
    }

    /** Lean's recursor_val::get_major_induct: the inductive of the major premise, from the type. */
    private static Name getMajorInductName(ConstantInfo rec) {
        int majorIdx = rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices;
        Expr t = rec.type;
        for (int i = 0; i < majorIdx; i++) {
            if (t.tag != Expr.FORALL) return null;
            t = (Expr) t.o2;
        }
        if (t.tag != Expr.FORALL) return null;
        Expr head = getAppFn((Expr) t.o1);
        return head.tag == Expr.CONST ? (Name) head.o0 : null;
    }

    /** Lean's to_cnstr_when_K: a K-like major becomes the nullary constructor when its type allows. */
    private Expr toCnstrWhenK(ConstantInfo rec, Expr e, boolean cheapRec, boolean cheapProj) {
        Expr appType = recWhnf(inferFn.infer(e), cheapRec, cheapProj);
        Expr I = getAppFn(appType);
        if (I.tag != Expr.CONST || !I.o0.equals(getMajorInductName(rec))) return e;
        Expr[] typeArgs = (Expr[]) getAppFnArgs(appType)[1];
        // has_expr_mvar: universe metavariables do not block K
        if (appType.hasMVar())
            for (int i = rec.numParams; i < typeArgs.length; i++)
                if (Expr.hasExprMVar(typeArgs[i])) return e;
        Expr newCnstr = mkNullaryCnstr(appType, rec.numParams);
        if (newCnstr == null) return e;
        return isDefEqFn.isDefEq(appType, inferFn.infer(newCnstr)) ? newCnstr : e;
    }

    /** Lean's mk_nullary_cnstr: the first constructor applied to the type's parameters. */
    private Expr mkNullaryCnstr(Expr type, int numParams) {
        Object[] fa = getAppFnArgs(type);
        Expr d = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        if (d.tag != Expr.CONST || args.length < numParams) return null;
        ConstantInfo ind = env.lookup((Name) d.o0);
        if (ind == null || !ind.isInduct() || ind.ctors.length == 0) return null;
        return mkApps(Expr.mkConstOwned(ind.ctors[0], d.o1), java.util.Arrays.copyOf(args, numParams));
    }

    /** Lean's is_non_rec_structure (inductive.cpp): `env.get`, so an unknown name is an error. */
    static boolean isNonRecStructure(Env env, Name n) {
        ConstantInfo ci = env.lookupOrThrow(n);
        return ci.isInduct() && ci.ctors.length == 1 && ci.numIndices == 0 && !ci.isRec;
    }

    private boolean isConstructorApp(Expr e) {
        Expr fn = getAppFn(e);
        if (fn.tag != Expr.CONST) return false;
        ConstantInfo ci = env.lookup((Name) fn.o0);
        return ci != null && ci.isCtor();
    }

    /** Lean's to_cnstr_when_structure: a non-constructor of a non-Prop structure becomes `mk e.1 … e.n`. */
    private Expr toCnstrWhenStructure(Name induct, Expr e, boolean cheapRec, boolean cheapProj) {
        if (!structureEta || induct == null || !isNonRecStructure(env, induct) || isConstructorApp(e)) return e;
        Expr eType = recWhnf(inferFn.infer(e), cheapRec, cheapProj);
        Expr I = getAppFn(eType);
        if (I.tag != Expr.CONST || !I.o0.equals(induct)) return e;
        if (isPropFn.isProp(eType)) return e;
        return expandEtaStruct(eType, e);
    }

    /** Lean's expand_eta_struct. */
    private Expr expandEtaStruct(Expr eType, Expr e) {
        Object[] fa = getAppFnArgs(eType);
        Expr I = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        ConstantInfo ind = env.lookup((Name) I.o0);
        if (ind == null || ind.ctors.length == 0) return e;
        ConstantInfo ctor = env.lookupOrThrow(ind.ctors[0]);
        Expr r = mkApps(Expr.mkConstOwned(ctor.name, I.o1), java.util.Arrays.copyOf(args, Math.min(ctor.numParams, args.length)));
        for (int i = 0; i < ctor.numFields; i++) r = Expr.app(r, Expr.proj(I.o0, i, e));
        return r;
    }

    /** Lean's string_lit_to_constructor: `String.ofList [Char.ofNat c₁, …]` over the code points. */
    static Expr stringLitToConstructor(Expr e) {
        Expr charType = Expr.mkConstOwned(Name.CHAR, NO_LEVELS);
        Object[] zero = {Level.ZERO_LEVEL};
        Expr nil = Expr.app(Expr.mkConstOwned(Name.LIST_NIL, zero), charType);
        Expr cons = Expr.app(Expr.mkConstOwned(Name.LIST_CONS, zero), charType);
        Expr ofNat = Expr.mkConstOwned(Name.CHAR_OF_NAT, NO_LEVELS);
        int[] cps = ((String) e.o0).codePoints().toArray();
        Expr r = nil;
        for (int i = cps.length - 1; i >= 0; i--)
            r = Expr.app(Expr.app(cons, Expr.app(ofNat, Expr.litNat(BigInteger.valueOf(cps[i])))), r);
        return Expr.app(Expr.mkConstOwned(Name.STRING_OF_LIST, NO_LEVELS), r);
    }

    /** Lean's quot_reduce_rec: Quot.lift (major 5) / Quot.ind (major 4) on `Quot.mk _ _ a`. */
    private Expr quotReduceRec(Expr e) {
        Object[] fa = getAppFnArgs(e);
        Expr fn = (Expr) fa[0];
        Expr[] args = (Expr[]) fa[1];
        if (fn.tag != Expr.CONST) return null;
        int mkPos;
        if (Name.QUOT_LIFT.equals(fn.o0)) mkPos = 5;
        else if (Name.QUOT_IND.equals(fn.o0)) mkPos = 4;
        else return null;
        if (args.length <= mkPos) return null;
        Expr mk = whnf(args[mkPos]);
        Object[] ma = getAppFnArgs(mk);
        Expr mkFn = (Expr) ma[0];
        Expr[] mkArgs = (Expr[]) ma[1];
        if (mkFn.tag != Expr.CONST || !Name.QUOT_MK.equals(mkFn.o0) || mkArgs.length != 3) return null;
        return mkApps(Expr.app(args[3], mkArgs[2]), args, mkPos + 1);
    }

    // ============================================================
    // Projections (Lean's reduce_proj / reduce_proj_core)
    // ============================================================

    /** Lean's reduce_proj_core: field `idx` of a constructor of structure `sname` (a string
     *  literal is expanded first). Null when `c` is no such constructor application. */
    public Expr reduceProjCore(Expr c, Name sname, long idx) {
        if (c.tag == Expr.LIT_STR) c = whnf(stringLitToConstructor(c));
        Object[] fa = getAppFnArgs(c);
        Expr mk = (Expr) fa[0];
        if (mk.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookupOrThrow((Name) mk.o0);   // env().get
        if (!ci.isCtor() || !ci.inductName.equals(sname)) return null;
        return projField(ci, (Expr[]) fa[1], idx);
    }

    /** Lean's reduce_proj. */
    private Expr reduceProj(Expr e, boolean cheapRec, boolean cheapProj) {
        if (e.longVal < 0 || e.longVal > 0xFFFFFFFFL) return null;   // to_proj_idx
        Expr c = cheapProj ? whnfCoreImpl((Expr) e.o1, cheapRec, cheapProj) : whnf((Expr) e.o1);
        return reduceProjCore(c, (Name) e.o0, e.longVal);
    }

    /**
     * Field `idx` of a constructor application with arguments `args`, or null when the index is
     * past the last argument. Compares before adding the parameter count, so no index wraps.
     */
    static Expr projField(ConstantInfo ctor, Expr[] args, long idx) {
        if (idx < 0 || idx >= (long) args.length - ctor.numParams) return null;
        return args[(int) (ctor.numParams + idx)];
    }

    // ============================================================
    // Delta (Lean's is_delta, unfold_definition)
    // ============================================================

    /** Lean's is_delta: the head constant of `e` has a value and is applied to its universe
     *  arity (and the current transparency lets it unfold). An unknown head is no candidate. */
    ConstantInfo isDelta(Expr e) {
        Expr head = getAppFn(e);
        if (head.tag != Expr.CONST) return null;
        ConstantInfo ci = env.lookup((Name) head.o0);
        if (ci == null || ci.getValue() == null || ci.levelParams.length != constLevels(head).length) return null;
        return canUnfold((Name) head.o0) ? ci : null;
    }

    /** Lean's unfold_definition_core: the instantiated value of a delta constant. */
    private Expr unfoldDefinitionCore(Expr c) {
        ConstantInfo d = isDelta(c);
        if (d == null) return null;
        Object[] us = constLevels(c);
        if (us.length == 0) return d.getValue();
        Expr cached = unfoldCache.get(c);
        if (cached != null) return cached;
        Expr r = instantiateLevelParams(d.getValue(), makeLevelSubst(d.levelParams, us));
        unfoldCache.put(c, r);
        return r;
    }

    /** Lean's unfold_definition: unfold the head of `e` when it is a delta constant, else null. */
    public Expr unfoldDefinition(Expr e) {
        if (e.tag != Expr.APP) return unfoldDefinitionCore(e);
        Object[] fa = getAppFnArgs(e);
        Expr f = unfoldDefinitionCore((Expr) fa[0]);
        return f == null ? null : mkApps(f, (Expr[]) fa[1]);
    }

    /** The unfolded head constant `head` (kept for meta-level callers). */
    Expr tryUnfoldDef(Expr head) {
        return unfoldDefinitionCore(head);
    }

    // ============================================================
    // WHNF core (Lean's whnf_core: no delta, no native reduction)
    // ============================================================

    public Expr whnfCore(Expr e) {
        return whnfCoreImpl(e, false, false);
    }

    /** whnf_core with Lean's cheap flags. The cache is read under any flags (a more-reduced
     *  answer is still a whnf_core result) and written only without them. */
    public Expr whnfCore(Expr e, boolean cheapRec, boolean cheapProj) {
        return whnfCoreImpl(e, cheapRec, cheapProj);
    }

    private Expr whnfCoreImpl(Expr e, boolean cheapRec, boolean cheapProj) {
        switch (e.tag) {
            case Expr.BVAR: case Expr.SORT: case Expr.MVAR: case Expr.LAM: case Expr.FORALL:
            case Expr.CONST: case Expr.LIT_NAT: case Expr.LIT_STR:
                return e;
            case Expr.MDATA:
                checkFuel();
                mdataCount++;
                return whnfCoreImpl((Expr) e.o1, cheapRec, cheapProj);
            case Expr.FVAR:
                if (!isLetFVar(e)) return e;
                break;
            default:
                break;
        }

        Expr cached = whnfCoreCache.get(e);
        if (cached != null) {
            whnfCoreCacheHits++;
            return cached;
        }

        Expr r;
        switch (e.tag) {
            case Expr.FVAR:
                checkFuel();
                fvarLetCount++;
                return whnfCoreImpl((Expr) lctx.get(e.longVal)[3], cheapRec, cheapProj);
            case Expr.PROJ: {
                Expr p = reduceProj(e, cheapRec, cheapProj);
                if (p != null) {
                    checkFuel();
                    projCount++;
                    r = whnfCoreImpl(p, cheapRec, cheapProj);
                } else {
                    r = e;
                }
                break;
            }
            case Expr.APP: {
                Object[] fa = getAppFnArgs(e);
                Expr f0 = (Expr) fa[0];
                Expr[] args = (Expr[]) fa[1];
                Expr f = whnfCoreImpl(f0, cheapRec, cheapProj);
                if (f.tag == Expr.LAM) {
                    checkFuel();
                    betaCount++;
                    int m = 1;
                    while (((Expr) f.o2).tag == Expr.LAM && m < args.length) {
                        f = (Expr) f.o2;
                        m++;
                    }
                    r = whnfCoreImpl(mkApps(instantiateRev((Expr) f.o2, m, args, 0), args, m), cheapRec, cheapProj);
                } else if (LeanExprKey.exprEquals(f, f0)) {
                    Expr reduced = reduceRecursor(e, cheapRec, cheapProj);
                    if (reduced == null) return e;
                    checkFuel();
                    iotaCount++;
                    return whnfCoreImpl(reduced, cheapRec, cheapProj);
                } else {
                    checkFuel();
                    r = whnfCoreImpl(mkApps(f, args), cheapRec, cheapProj);
                }
                break;
            }
            case Expr.LET:
                checkFuel();
                zetaCount++;
                r = whnfCoreImpl(instantiate1((Expr) e.o3, (Expr) e.o2), cheapRec, cheapProj);
                break;
            default:
                return e;
        }

        if (!cheapRec && !cheapProj) whnfCoreCache.put(e, r);
        return r;
    }

    private boolean isLetFVar(Expr e) {
        if (lctx == null) return false;
        Object[] decl = lctx.get(e.longVal);
        return decl != null && decl[0] instanceof Number && ((Number) decl[0]).intValue() == 1;
    }

    // ============================================================
    // WHNF (Lean's whnf: whnf_core, native Nat reduction, delta, repeat)
    // ============================================================

    public Expr whnf(Expr e) {
        whnfCalls++;
        switch (e.tag) {
            case Expr.BVAR: case Expr.SORT: case Expr.MVAR: case Expr.FORALL:
            case Expr.LIT_NAT: case Expr.LIT_STR:
                return e;
            case Expr.MDATA:
                return whnf((Expr) e.o1);
            case Expr.FVAR:
                if (!isLetFVar(e)) return e;
                break;
            default:
                break;
        }
        Expr cached = whnfCache.get(e);
        if (cached != null) { whnfCacheHits++; return cached; }
        whnfDepth++;
        if (whnfDepth > whnfMaxDepth) {
            whnfMaxDepth = whnfDepth;
            whnfMaxDepthExpr = e;
        }
        try {
            Expr t = e;
            while (true) {
                Expr t1 = whnfCore(t);
                Expr v = reduceNat(t1);
                if (v != null) {
                    whnfCache.put(e, v);
                    return v;
                }
                Expr next = unfoldDefinition(t1);
                if (next == null) {
                    whnfCache.put(e, t1);
                    return t1;
                }
                checkFuel();
                deltaCount++;
                t = next;
            }
        } finally {
            whnfDepth--;
        }
    }

    // ============================================================
    // Helper methods
    // ============================================================

    /** Extract levels from a CONST expression as a list for iteration. */
    @SuppressWarnings("unchecked")
    static Object[] constLevels(Expr e) {
        Object levels = e.o1;
        if (levels instanceof LevelList) return ((LevelList) levels).arr;   // read-only use
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

    /** The reducer's caches, for diagnostics. */
    public java.util.Map<String, ExprMap<Expr>> caches() {
        java.util.LinkedHashMap<String, ExprMap<Expr>> m = new java.util.LinkedHashMap<>();
        m.put("whnfCore", whnfCoreCache); m.put("whnf", whnfCache); m.put("unfold", unfoldCache);
        return m;
    }

    /** Clear all caches (call when starting a new declaration check). */
    public void clearCaches() {
        whnfCoreCache.clear();
        whnfCache.clear();
        unfoldCache.clear();
    }
}
