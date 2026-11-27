package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * A local context for declaration construction — Lean's {@code local_ctx} with its name
 * generator: free variables with fixed types, numbered from a private base so they never
 * collide with the ids a {@link TypeChecker} allocates (KERNEL_FRESH_BASE) or with another
 * context's. {@link #mkPi}/{@link #mkLambda} abstract a telescope using each local's user
 * name, type and binder info, as {@code local_ctx::mk_pi}/{@code mk_lambda}.
 */
final class LocalCtx {
    private final HashMap<Long, LocalDecl> decls = new HashMap<>();
    private final ArrayList<LocalDecl> order = new ArrayList<>();
    private long next;

    LocalCtx(long base) {
        this.next = base;
    }

    Expr mkLocalDecl(Object name, Expr type, Object binderInfo) {
        LocalDecl d = new LocalDecl(next++, name, type, binderInfo);
        decls.put(d.id, d);
        order.add(d);
        return d.fvar;
    }

    LocalDecl get(Expr fvar) {
        LocalDecl d = decls.get(fvar.longVal);
        if (fvar.tag != Expr.FVAR || d == null) throw new IllegalStateException("unknown local " + fvar);
        return d;
    }

    int size() {
        return order.size();
    }

    LocalDecl at(int i) {
        return order.get(i);
    }

    /** Register the locals [from, size) with a checker. */
    void addTo(TypeChecker tc, int from) {
        for (int i = from; i < order.size(); i++) {
            LocalDecl d = order.get(i);
            tc.addLocalDecl(d.id, d.name, d.type);
        }
    }

    Expr mkPi(List<Expr> fvars, Expr body) {
        return mkBinding(fvars, body, true);
    }

    Expr mkLambda(List<Expr> fvars, Expr body) {
        return mkBinding(fvars, body, false);
    }

    private Expr mkBinding(List<Expr> fvars, Expr body, boolean pi) {
        int n = fvars.size();
        if (n == 0) return body;
        long[] ids = new long[n];
        for (int i = 0; i < n; i++) ids[i] = get(fvars.get(i)).id;
        Expr r = Reducer.abstractFvars(body, n, ids);
        for (int i = n - 1; i >= 0; i--) {
            LocalDecl d = decls.get(ids[i]);
            Expr domain = Reducer.abstractFvars(d.type, i, ids);
            r = pi ? Expr.forall(d.name, domain, r, d.binderInfo) : Expr.lam(d.name, domain, r, d.binderInfo);
        }
        return r;
    }
}
