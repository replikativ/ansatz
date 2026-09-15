package ansatz.kernel;

/**
 * Lean's {@code expr_pair_set} (type_checker.h:29): a set of ordered expression pairs under
 * structural equality, hashed by {@code hash(hash(first), hash(second))} (expr.h
 * expr_pair_hash). The is_def_eq success and failure caches of lean4#14806 — one flat entry
 * per pair, never an equivalence class, never a container per left-hand side.
 */
public final class ExprPairSet {
    private Expr[] as;
    private Expr[] bs;
    private int[] hashes;
    private int size;

    public ExprPairSet(int expected) {
        int cap = 16;
        while (cap < expected * 2) cap <<= 1;
        as = new Expr[cap];
        bs = new Expr[cap];
        hashes = new int[cap];
    }

    private static int pairHash(Expr a, Expr b) {
        int h = a.structuralHash() * 31 + b.structuralHash();
        h *= 0x9E3779B1;
        return h ^ (h >>> 16);
    }

    private static boolean same(Expr k, Expr e) {
        return k == e || LeanExprKey.exprEquals(k, e);
    }

    public boolean contains(Expr a, Expr b) {
        int h = pairHash(a, b);
        int mask = as.length - 1;
        int i = h & mask;
        while (true) {
            Expr k = as[i];
            if (k == null) return false;
            if (hashes[i] == h && same(k, a) && same(bs[i], b)) return true;
            i = (i + 1) & mask;
        }
    }

    public void add(Expr a, Expr b) {
        if (size * 2 >= as.length) grow();
        int h = pairHash(a, b);
        int mask = as.length - 1;
        int i = h & mask;
        while (true) {
            Expr k = as[i];
            if (k == null) { as[i] = a; bs[i] = b; hashes[i] = h; size++; return; }
            if (hashes[i] == h && same(k, a) && same(bs[i], b)) return;
            i = (i + 1) & mask;
        }
    }

    private void grow() {
        Expr[] oa = as, ob = bs; int[] oh = hashes;
        int cap = oa.length * 2;
        as = new Expr[cap]; bs = new Expr[cap]; hashes = new int[cap];
        int mask = cap - 1;
        for (int j = 0; j < oa.length; j++) {
            if (oa[j] == null) continue;
            int i = oh[j] & mask;
            while (as[i] != null) i = (i + 1) & mask;
            as[i] = oa[j]; bs[i] = ob[j]; hashes[i] = oh[j];
        }
    }

    public int size() { return size; }

    public void clear() {
        if (size == 0) return;
        java.util.Arrays.fill(as, null);
        java.util.Arrays.fill(bs, null);
        size = 0;
    }
}
