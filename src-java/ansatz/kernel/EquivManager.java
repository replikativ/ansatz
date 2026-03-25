// Ansatz kernel — Union-find for proven expression equalities.

package ansatz.kernel;

import java.util.ArrayList;
import java.util.IdentityHashMap;

/**
 * Union-find (disjoint set) structure for tracking proven expression equalities.
 * Port of Lean 4's equiv_manager.cpp.
 *
 * <p>When two expressions are proven definitionally equal, they are merged.
 * Future checks between any two expressions in the same equivalence class
 * return true in O(alpha(n)) time.
 */
public final class EquivManager {

    private final ArrayList<int[]> nodes;  // [parent, rank]
    private final IdentityHashMap<Expr, Integer> toNode;

    public EquivManager() {
        this.nodes = new ArrayList<>(256);
        this.toNode = new IdentityHashMap<>(256);
    }

    private int allocNode() {
        int id = nodes.size();
        nodes.add(new int[]{id, 0}); // parent=self, rank=0
        return id;
    }

    private int getOrCreateNode(Expr e) {
        Integer id = toNode.get(e);
        if (id != null) return id;
        int newId = allocNode();
        toNode.put(e, newId);
        return newId;
    }

    private int find(int n) {
        // Path compression
        int root = n;
        while (nodes.get(root)[0] != root) root = nodes.get(root)[0];
        // Compress path
        while (n != root) {
            int next = nodes.get(n)[0];
            nodes.get(n)[0] = root;
            n = next;
        }
        return root;
    }

    private void merge(int n1, int n2) {
        int r1 = find(n1), r2 = find(n2);
        if (r1 == r2) return;
        int rank1 = nodes.get(r1)[1], rank2 = nodes.get(r2)[1];
        if (rank1 < rank2) {
            nodes.get(r1)[0] = r2;
        } else if (rank1 > rank2) {
            nodes.get(r2)[0] = r1;
        } else {
            nodes.get(r2)[0] = r1;
            nodes.get(r1)[1]++;
        }
    }

    /**
     * Check if two expressions are equivalent via deep structural comparison
     * with union-find merging. Matches Lean 4's equiv_manager::is_equiv_core.
     *
     * Key difference from Expr.equals: ignores binding names/info for Lambda/Pi,
     * and merges equivalence classes as sub-expressions are proven equal.
     */
    public boolean isEquiv(Expr a, Expr b) {
        return isEquivCore(a, b, true);
    }

    public boolean isEquiv(Expr a, Expr b, boolean useHash) {
        return isEquivCore(a, b, useHash);
    }

    private boolean isEquivCore(Expr a, Expr b, boolean useHash) {
        if (a.isEqp(b)) return true;
        // Hash fast-reject: skip for LAM/FORALL (alpha-equiv ignores binder names).
        // Use Level-normalized hash for expressions to handle equivalent-but-
        // differently-structured levels correctly.
        if (useHash && a.tag != Expr.LAM && a.tag != Expr.FORALL
                    && b.tag != Expr.LAM && b.tag != Expr.FORALL
                    && equivHash(a) != equivHash(b)) return false;
        if (a.tag == Expr.BVAR && b.tag == Expr.BVAR) return a.longVal == b.longVal;

        int r1 = find(getOrCreateNode(a));
        int r2 = find(getOrCreateNode(b));
        if (r1 == r2) return true;

        if (a.tag != b.tag) return false;

        boolean result;
        switch (a.tag) {
            case Expr.BVAR:
                result = a.longVal == b.longVal;
                break;
            case Expr.CONST:
                // Compare name and universe levels
                result = a.o0.equals(b.o0) && levelsEqual(a.o1, b.o1);
                break;
            case Expr.FVAR:
                result = a.longVal == b.longVal;
                break;
            case Expr.APP:
                result = isEquivCore((Expr) a.o0, (Expr) b.o0, useHash) &&
                         isEquivCore((Expr) a.o1, (Expr) b.o1, useHash);
                break;
            case Expr.LAM: case Expr.FORALL:
                // Lean ignores binding name/info — only compares domain and body
                result = isEquivCore((Expr) a.o1, (Expr) b.o1, useHash) &&
                         isEquivCore((Expr) a.o2, (Expr) b.o2, useHash);
                break;
            case Expr.SORT:
                result = Level.eq((Level) a.o0, (Level) b.o0);
                break;
            case Expr.LIT_NAT:
                result = a.o0.equals(b.o0);
                break;
            case Expr.LIT_STR:
                result = a.o0.equals(b.o0);
                break;
            case Expr.MDATA:
                result = isEquivCore((Expr) a.o1, (Expr) b.o1, useHash);
                break;
            case Expr.PROJ:
                result = a.o0.equals(b.o0) && a.longVal == b.longVal &&
                         isEquivCore((Expr) a.o1, (Expr) b.o1, useHash);
                break;
            case Expr.LET:
                result = isEquivCore((Expr) a.o1, (Expr) b.o1, useHash) &&
                         isEquivCore((Expr) a.o2, (Expr) b.o2, useHash) &&
                         isEquivCore((Expr) a.o3, (Expr) b.o3, useHash);
                break;
            default:
                result = false;
        }
        if (result) merge(r1, r2);
        return result;
    }

    /** Compare universe level lists for structural equality. */
    @SuppressWarnings("unchecked")
    private static boolean levelsEqual(Object levels1, Object levels2) {
        if (levels1 == levels2) return true;
        if (levels1 == null || levels2 == null) return false;
        // Handle both Object[] and List<Object> representations
        java.util.List<Object> ls1 = levels1 instanceof Object[]
            ? java.util.Arrays.asList((Object[]) levels1)
            : (java.util.List<Object>) levels1;
        java.util.List<Object> ls2 = levels2 instanceof Object[]
            ? java.util.Arrays.asList((Object[]) levels2)
            : (java.util.List<Object>) levels2;
        if (ls1.size() != ls2.size()) return false;
        for (int i = 0; i < ls1.size(); i++) {
            if (!Level.eq((Level) ls1.get(i), (Level) ls2.get(i))) return false;
        }
        return true;
    }

    // Cache for equivHash — avoids recomputing for DAG-shared sub-expressions
    private final IdentityHashMap<Expr, Integer> equivHashCache = new IdentityHashMap<>(256);

    /**
     * Hash that normalizes levels, matching Level.eq semantics.
     * Recursive: compound expressions combine children's equivHashes.
     * Cached per expression identity for DAG sharing.
     */
    private int equivHash(Expr e) {
        // Fast path: if no level params, structural hash is correct
        if (!e.hasLevelParam()) return e.structuralHash();
        Integer cached = equivHashCache.get(e);
        if (cached != null) return cached;
        int h = equivHashGo(e);
        equivHashCache.put(e, h);
        return h;
    }

    private int equivHashGo(Expr e) {
        switch (e.tag) {
            case Expr.SORT:
                return Level.simplify((Level) e.o0).hashCode() * 31 + Expr.SORT;
            case Expr.CONST: {
                int h = e.o0.hashCode(); // name
                Object levels = e.o1;
                if (levels instanceof Object[]) {
                    for (Object l : (Object[]) levels)
                        h = h * 31 + Level.simplify((Level) l).hashCode();
                } else if (levels instanceof clojure.lang.IPersistentVector) {
                    clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) levels;
                    for (int i = 0; i < v.count(); i++)
                        h = h * 31 + Level.simplify((Level) v.nth(i)).hashCode();
                }
                return h * 31 + Expr.CONST;
            }
            case Expr.APP:
                return (equivHash((Expr) e.o0) * 31 + equivHash((Expr) e.o1)) * 31 + Expr.APP;
            case Expr.LAM: case Expr.FORALL:
                // Ignore binder name/info (alpha-equiv)
                return (equivHash((Expr) e.o1) * 31 + equivHash((Expr) e.o2)) * 31 + e.tag;
            case Expr.PROJ:
                return (e.o0.hashCode() * 31 + equivHash((Expr) e.o1)) * 31 + Expr.PROJ + (int) e.longVal;
            default:
                return e.structuralHash();
        }
    }

    /**
     * Record that two expressions are definitionally equal.
     */
    public void addEquiv(Expr e1, Expr e2) {
        int n1 = getOrCreateNode(e1);
        int n2 = getOrCreateNode(e2);
        merge(n1, n2);
    }

    public void clear() {
        nodes.clear();
        toNode.clear();
        equivHashCache.clear();
    }
}
