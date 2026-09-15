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
