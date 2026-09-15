package ansatz.kernel;

import java.util.Objects;

/**
 * Hash-map key matching Lean kernel `expr_map` equality.
 *
 * Lean's structural expression equality ignores binder names/info for lambdas,
 * Pis, and lets, but it still compares metadata payloads and projection
 * structure names. This is intentionally different from both Java Expr.equals
 * and the (pair-keyed, lean4#14806) is_def_eq success/failure caches.
 */
public final class LeanExprKey {
    final Expr expr;
    private final int hash;

    public LeanExprKey(Expr expr) {
        this.expr = expr;
        this.hash = hashExpr(expr);
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        return this == obj || (obj instanceof LeanExprKey
                && hash == ((LeanExprKey) obj).hash
                && exprEquals(expr, ((LeanExprKey) obj).expr));
    }

    /** Lean's `hash(e)`: the hash stored in the node at construction (expr.h:131), which
     *  ignores binder names/info and mdata payloads exactly as exprEquals does. */
    static int hashExpr(Expr e) {
        return e.structuralHash();
    }

    /** Lean's `is_equal` (expr_eq_fn.cpp, CompareBinderInfo = false). */
    static boolean exprEquals(Expr a, Expr b) {
        if (a.isEqp(b)) return true;
        if (a.structuralHash() != b.structuralHash()) return false;
        return new EqFn().apply(a, b, true);
    }

    /**
     * A port of `expr_eq_fn`: structural equality that (1) rejects on the stored hash before
     * looking at either node, (2) walks an application spine iteratively, argument first, and
     * (3) memoizes the pairs of composite nodes it has entered, so two structurally equal DAGs
     * are compared once per shared pair instead of once per path — the terms the kernel
     * compares are DAGs with heavy sharing (instantiated definitions, structure towers), and
     * without the memo a comparison walks their tree expansions. Lean memoizes the pairs whose
     * nodes are `is_shared` (refcount > 1); the JVM has no refcounts, so the memo starts after
     * PAIR_MEMO_THRESHOLD composite pairs — a comparison that stays small never allocates.
     */
    private static final class EqFn {
        private static final int PAIR_MEMO_THRESHOLD = 64;
        private int composites;
        private PairMemo memo;

        private boolean checkCache(Expr a, Expr b) {
            if (composites++ < PAIR_MEMO_THRESHOLD) return false;
            if (memo == null) memo = new PairMemo();
            return !memo.add(a, b);
        }

        boolean apply(Expr a, Expr b, boolean root) {
            if (a.isEqp(b)) return true;
            if (a.structuralHash() != b.structuralHash()) return false;
            if (a.tag != b.tag) return false;
            switch (a.tag) {
                case Expr.BVAR:
                case Expr.FVAR:
                case Expr.MVAR:
                    return a.longVal == b.longVal;
                case Expr.SORT:
                    return Objects.equals(a.o0, b.o0);
                case Expr.LIT_NAT:
                case Expr.LIT_STR:
                    return Objects.equals(a.o0, b.o0);
                case Expr.CONST:
                    return Objects.equals(a.o0, b.o0) && Expr.levelsEquals(a.o1, b.o1);
                default:
                    break;
            }
            if (!root && checkCache(a, b)) return true;
            switch (a.tag) {
                case Expr.MDATA:
                    return apply((Expr) a.o1, (Expr) b.o1, false)
                        && Objects.equals(a.o0, b.o0);
                case Expr.PROJ:
                    return apply((Expr) a.o1, (Expr) b.o1, false)
                        && Objects.equals(a.o0, b.o0)
                        && a.longVal == b.longVal;
                case Expr.APP: {
                    if (!apply((Expr) a.o1, (Expr) b.o1, false)) return false;
                    Expr ca = (Expr) a.o0, cb = (Expr) b.o0;
                    while (true) {
                        if (ca.tag != Expr.APP) break;
                        if (cb.tag != Expr.APP) return false;
                        if (!apply((Expr) ca.o1, (Expr) cb.o1, false)) return false;
                        ca = (Expr) ca.o0;
                        cb = (Expr) cb.o0;
                    }
                    return apply(ca, cb, false);
                }
                case Expr.LAM:
                case Expr.FORALL:
                    return apply((Expr) a.o1, (Expr) b.o1, false)
                        && apply((Expr) a.o2, (Expr) b.o2, false);
                case Expr.LET:
                    return apply((Expr) a.o1, (Expr) b.o1, false)
                        && apply((Expr) a.o2, (Expr) b.o2, false)
                        && apply((Expr) a.o3, (Expr) b.o3, false);
                default:
                    return a.equals(b);
            }
        }
    }

    /** An open-addressed set of (Expr, Expr) pairs compared by identity — the memo of
     *  `expr_eq_fn`. Identity hash codes only choose the slot; membership is `==` on both
     *  references, so a hash collision can never make two distinct pairs one. */
    public static final class PairMemo {
        private Expr[] as = new Expr[64];
        private Expr[] bs = new Expr[64];
        private int size;

        private static int slot(Expr a, Expr b, int mask) {
            int h = System.identityHashCode(a) * 31 + System.identityHashCode(b);
            h ^= (h >>> 16);
            return h & mask;
        }

        /** Adds the pair; false if it was already present. */
        public boolean add(Expr a, Expr b) {
            if (size * 2 >= as.length) grow();
            int mask = as.length - 1;
            int i = slot(a, b, mask);
            while (true) {
                Expr x = as[i];
                if (x == null) { as[i] = a; bs[i] = b; size++; return true; }
                if (x == a && bs[i] == b) return false;
                i = (i + 1) & mask;
            }
        }

        private void grow() {
            Expr[] oa = as, ob = bs;
            as = new Expr[oa.length * 2];
            bs = new Expr[oa.length * 2];
            int mask = as.length - 1;
            for (int j = 0; j < oa.length; j++) {
                if (oa[j] == null) continue;
                int i = slot(oa[j], ob[j], mask);
                while (as[i] != null) i = (i + 1) & mask;
                as[i] = oa[j]; bs[i] = ob[j];
            }
        }

        public int size() { return size; }
    }
}
