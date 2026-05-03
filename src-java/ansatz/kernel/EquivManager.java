// Ansatz kernel — Union-find for proven expression equalities.

package ansatz.kernel;

import java.util.ArrayList;
import java.util.HashMap;

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
    private final HashMap<LeanExprKey, Integer> toNode;

    public EquivManager() {
        this.nodes = new ArrayList<>(256);
        this.toNode = new HashMap<>(256);
    }

    private int allocNode() {
        int id = nodes.size();
        nodes.add(new int[]{id, 0}); // parent=self, rank=0
        return id;
    }

    private int getOrCreateNode(Expr e) {
        LeanExprKey key = new LeanExprKey(e);
        Integer id = toNode.get(key);
        if (id != null) return id;
        int newId = allocNode();
        toNode.put(key, newId);
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
     * Key differences from Expr.equals: ignores binding names/info for Lambda/Pi,
     * metadata payloads, and projection structure names; merges equivalence
     * classes as sub-expressions are proven equal.
     */
    public boolean isEquiv(Expr a, Expr b) {
        return isEquivCore(a, b, true);
    }

    public boolean isEquiv(Expr a, Expr b, boolean useHash) {
        return isEquivCore(a, b, useHash);
    }

    private boolean isEquivCore(Expr a, Expr b, boolean useHash) {
        if (a.isEqp(b)) return true;
        if (useHash && LeanExprKey.hashExpr(a) != LeanExprKey.hashExpr(b)) return false;
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
                // Lean's equiv_manager uses syntactic level equality here, not
                // semantic universe equality (`is_equivalent`).
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
                result = a.o0.equals(b.o0);
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
                // Lean's equiv_manager ignores the projection structure name and
                // compares only the field index and projected expression.
                result = a.longVal == b.longVal && isEquivCore((Expr) a.o1, (Expr) b.o1, useHash);
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

    private static boolean levelsEqual(Object levels1, Object levels2) {
        return Expr.levelsEquals(levels1, levels2);
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
    }
}
