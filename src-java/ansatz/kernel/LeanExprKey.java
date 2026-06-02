package ansatz.kernel;

import java.math.BigInteger;
import java.util.IdentityHashMap;
import java.util.Objects;

/**
 * Hash-map key matching Lean kernel `expr_map` equality.
 *
 * Lean's structural expression equality ignores binder names/info for lambdas,
 * Pis, and lets, but it still compares metadata payloads and projection
 * structure names. This is intentionally different from both Java Expr.equals
 * and EquivManager's broader equivalence relation.
 */
final class LeanExprKey {
    final Expr expr;
    private final int hash;
    private static final ThreadLocal<IdentityHashMap<Expr, Integer>> HASH_CACHE =
        ThreadLocal.withInitial(() -> new IdentityHashMap<>(16384));

    LeanExprKey(Expr expr) {
        this.expr = expr;
        this.hash = hashExpr(expr);
    }

    static void clearThreadCache() {
        HASH_CACHE.remove();
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

    static int hashExpr(Expr e) {
        IdentityHashMap<Expr, Integer> cache = HASH_CACHE.get();
        Integer cached = cache.get(e);
        if (cached != null) return cached;
        int h = hashExprUncached(e);
        cache.put(e, h);
        return h;
    }

    private static int hashExprUncached(Expr e) {
        switch (e.tag) {
            case Expr.BVAR:
            case Expr.FVAR:
            case Expr.MVAR:
                return Long.hashCode(e.longVal) * 31 + e.tag;
            case Expr.SORT:
                return Objects.hashCode(e.o0) * 31 + Expr.SORT;
            case Expr.CONST:
                return (Objects.hashCode(e.o0) * 31 + Expr.levelsHashCode(e.o1)) * 31 + Expr.CONST;
            case Expr.APP:
                return (hashExpr((Expr) e.o0) * 31 + hashExpr((Expr) e.o1)) * 31 + Expr.APP;
            case Expr.LAM:
                return (hashExpr((Expr) e.o1) * 31 + hashExpr((Expr) e.o2)) * 31 + Expr.LAM;
            case Expr.FORALL:
                return (hashExpr((Expr) e.o1) * 31 + hashExpr((Expr) e.o2)) * 31 + Expr.FORALL;
            case Expr.LET:
                return (((hashExpr((Expr) e.o1) * 31 + hashExpr((Expr) e.o2)) * 31
                        + hashExpr((Expr) e.o3)) * 31 + Expr.LET);
            case Expr.LIT_NAT:
                return ((BigInteger) e.o0).hashCode() * 31 + Expr.LIT_NAT;
            case Expr.LIT_STR:
                return e.o0.hashCode() * 31 + Expr.LIT_STR;
            case Expr.MDATA:
                // Lean's expression hash ignores the metadata payload.
                return hashExpr((Expr) e.o1) * 31 + Expr.MDATA;
            case Expr.PROJ:
                return ((Objects.hashCode(e.o0) * 31 + Long.hashCode(e.longVal)) * 31
                        + hashExpr((Expr) e.o1)) * 31 + Expr.PROJ;
            default:
                return e.structuralHash();
        }
    }

    static boolean exprEquals(Expr a, Expr b) {
        if (a.isEqp(b)) return true;
        if (a.tag != b.tag) return false;
        switch (a.tag) {
            case Expr.BVAR:
            case Expr.FVAR:
            case Expr.MVAR:
                return a.longVal == b.longVal;
            case Expr.SORT:
                return Objects.equals(a.o0, b.o0);
            case Expr.CONST:
                return Objects.equals(a.o0, b.o0) && Expr.levelsEquals(a.o1, b.o1);
            case Expr.APP:
                return exprEquals((Expr) a.o0, (Expr) b.o0)
                    && exprEquals((Expr) a.o1, (Expr) b.o1);
            case Expr.LAM:
            case Expr.FORALL:
                return exprEquals((Expr) a.o1, (Expr) b.o1)
                    && exprEquals((Expr) a.o2, (Expr) b.o2);
            case Expr.LET:
                return exprEquals((Expr) a.o1, (Expr) b.o1)
                    && exprEquals((Expr) a.o2, (Expr) b.o2)
                    && exprEquals((Expr) a.o3, (Expr) b.o3);
            case Expr.LIT_NAT:
            case Expr.LIT_STR:
                return Objects.equals(a.o0, b.o0);
            case Expr.MDATA:
                return Objects.equals(a.o0, b.o0)
                    && exprEquals((Expr) a.o1, (Expr) b.o1);
            case Expr.PROJ:
                return Objects.equals(a.o0, b.o0)
                    && a.longVal == b.longVal
                    && exprEquals((Expr) a.o1, (Expr) b.o1);
            default:
                return a.equals(b);
        }
    }
}
