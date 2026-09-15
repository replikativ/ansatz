package ansatz.kernel;

/**
 * Lean's {@code expr_map<T>} (expr_maps.h): a map from expressions under Lean's structural
 * equality — {@link LeanExprKey#exprEquals}, binder names and info ignored — hashed by the
 * hash stored in the node. Open addressing over parallel arrays: no wrapper key objects and
 * no entry nodes, so a cache of millions of entries costs three slots per entry; identity is
 * the first thing a probe tests, so the pointer-sharing fast path costs nothing extra.
 * Entries are never removed; the kernel clears a cache whole between declarations.
 */
public final class ExprMap<V> {
    private Expr[] keys;
    private Object[] vals;
    private int[] hashes;
    private int size;

    public ExprMap(int expected) {
        int cap = 16;
        while (cap < expected * 2) cap <<= 1;
        keys = new Expr[cap];
        vals = new Object[cap];
        hashes = new int[cap];
    }

    private static int mix(int h) {
        h *= 0x9E3779B1;
        return h ^ (h >>> 16);
    }

    @SuppressWarnings("unchecked")
    public V get(Expr e) {
        int h = e.structuralHash();
        int mask = keys.length - 1;
        int i = mix(h) & mask;
        while (true) {
            Expr k = keys[i];
            if (k == null) return null;
            if (k == e || (hashes[i] == h && LeanExprKey.exprEquals(k, e))) return (V) vals[i];
            i = (i + 1) & mask;
        }
    }

    public void put(Expr e, V v) {
        if (size * 2 >= keys.length) grow();
        int h = e.structuralHash();
        int mask = keys.length - 1;
        int i = mix(h) & mask;
        while (true) {
            Expr k = keys[i];
            if (k == null) { keys[i] = e; vals[i] = v; hashes[i] = h; size++; return; }
            if (k == e || (hashes[i] == h && LeanExprKey.exprEquals(k, e))) { vals[i] = v; return; }
            i = (i + 1) & mask;
        }
    }

    private void grow() {
        Expr[] ok = keys; Object[] ov = vals; int[] oh = hashes;
        int cap = ok.length * 2;
        keys = new Expr[cap]; vals = new Object[cap]; hashes = new int[cap];
        int mask = cap - 1;
        for (int j = 0; j < ok.length; j++) {
            if (ok[j] == null) continue;
            int i = mix(oh[j]) & mask;
            while (keys[i] != null) i = (i + 1) & mask;
            keys[i] = ok[j]; vals[i] = ov[j]; hashes[i] = oh[j];
        }
    }

    public int size() { return size; }

    /** Every key and value, for diagnostics. */
    public void forEach(java.util.function.BiConsumer<Expr, Object> f) {
        for (int i = 0; i < keys.length; i++) if (keys[i] != null) f.accept(keys[i], vals[i]);
    }

    public void clear() {
        if (size == 0) return;
        java.util.Arrays.fill(keys, null);
        java.util.Arrays.fill(vals, null);
        size = 0;
    }
}
