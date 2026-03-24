// Ansatz kernel — Universe levels with algebra and comparison.

package ansatz.kernel;

import java.util.HashMap;

/**
 * Universe level, matching Lean's Level type.
 *
 * <p>Levels form an algebra: zero, succ, max, imax, param.
 * Level comparison follows Lean 4's kernel level.cpp algorithm.
 *
 * <p>Memory: ~40 bytes per Level vs ~120 for Clojure tagged vectors.
 */
public final class Level {

    public static final byte ZERO = 0;
    public static final byte SUCC = 1;
    public static final byte MAX = 2;
    public static final byte IMAX = 3;
    public static final byte PARAM = 4;

    public final byte tag;
    public final int hash;
    public final Object o0;  // child 0: Level for SUCC/MAX/IMAX, Name for PARAM
    public final Object o1;  // child 1: Level for MAX/IMAX, null otherwise

    private Level(byte tag, int hash, Object o0, Object o1) {
        this.tag = tag;
        this.hash = hash;
        this.o0 = o0;
        this.o1 = o1;
    }

    // --- Singleton zero ---

    public static final Level ZERO_LEVEL = new Level(ZERO, 7, null, null);

    // --- Factories ---

    public static Level succ(Level l) {
        int h = l.hash * 31 + SUCC;
        return new Level(SUCC, h, l, null);
    }

    /** Raw max constructor — no normalization. Use max() for normalized construction. */
    private static Level maxRaw(Level l1, Level l2) {
        int h = (l1.hash * 31 + l2.hash) * 31 + MAX;
        return new Level(MAX, h, l1, l2);
    }

    /** Raw imax constructor — no normalization. Use imax() for normalized construction. */
    private static Level imaxRaw(Level l1, Level l2) {
        int h = (l1.hash * 31 + l2.hash) * 31 + IMAX;
        return new Level(IMAX, h, l1, l2);
    }

    /** Matching Lean 4's mk_max (level.cpp:81-103). Normalizes at construction time. */
    public static Level max(Level l1, Level l2) {
        // Both explicit (concrete numbers): return larger
        long n1 = toNat(l1), n2 = toNat(l2);
        if (n1 >= 0 && n2 >= 0) {
            return n1 >= n2 ? l1 : l2;
        }
        // Same level
        if (l1.equals(l2)) return l1;
        // max(0, l) = l, max(l, 0) = l
        if (l1.tag == ZERO) return l2;
        if (l2.tag == ZERO) return l1;
        // max(l1, max(l1, l')) = max(l1, l')
        if (l2.tag == MAX && (l2.maxLhs().equals(l1) || l2.maxRhs().equals(l1))) return l2;
        if (l1.tag == MAX && (l1.maxLhs().equals(l2) || l1.maxRhs().equals(l2))) return l1;
        // Same base with different offsets: max(succ^a b, succ^b b) = larger
        long[] off1 = new long[1], off2 = new long[1];
        Level base1 = getOffset(l1, off1), base2 = getOffset(l2, off2);
        if (base1.equals(base2) && off1[0] != off2[0]) {
            return off1[0] > off2[0] ? l1 : l2;
        }
        return maxRaw(l1, l2);
    }

    /** Matching Lean 4's mk_imax (level.cpp:112-123). Normalizes at construction time. */
    public static Level imax(Level l1, Level l2) {
        // imax(l1, l2) where l2 is known non-zero: reduce to max
        if (isNeverZero(l2)) return max(l1, l2);
        // imax(l1, 0) = 0
        if (l2.tag == ZERO) return l2;
        // imax(0, l2) = l2, imax(1, l2) = l2
        if (l1.tag == ZERO) return l2;
        if (l1.equals(fromNat(1))) return l2;
        // imax(l, l) = l
        if (l1.equals(l2)) return l1;
        return imaxRaw(l1, l2);
    }

    public static Level param(Object name) {
        int h = name.hashCode() * 31 + PARAM;
        return new Level(PARAM, h, name, null);
    }

    // --- Accessors ---

    public Level succPred() { return (Level) o0; }
    public Level maxLhs() { return (Level) o0; }
    public Level maxRhs() { return (Level) o1; }
    public Level imaxLhs() { return (Level) o0; }
    public Level imaxRhs() { return (Level) o1; }
    public Object paramName() { return o0; }

    // --- Predicates ---

    public static boolean hasParam(Level l) {
        switch (l.tag) {
            case ZERO: return false;
            case SUCC: return hasParam(l.succPred());
            case MAX: return hasParam(l.maxLhs()) || hasParam(l.maxRhs());
            case IMAX: return hasParam(l.imaxLhs()) || hasParam(l.imaxRhs());
            case PARAM: return true;
            default: return false;
        }
    }

    public static boolean isNeverZero(Level l) {
        switch (l.tag) {
            case ZERO: return false;
            case SUCC: return true;
            case MAX: return isNeverZero(l.maxLhs()) || isNeverZero(l.maxRhs());
            case IMAX: return isNeverZero(l.imaxRhs());
            case PARAM: return false;
            default: return false;
        }
    }

    /**
     * If level is a concrete natural number (no params), return it. Else return -1.
     */
    public static long toNat(Level l) {
        switch (l.tag) {
            case ZERO: return 0;
            case SUCC: {
                long n = toNat(l.succPred());
                return n >= 0 ? n + 1 : -1;
            }
            case MAX: {
                long a = toNat(l.maxLhs());
                long b = toNat(l.maxRhs());
                return (a >= 0 && b >= 0) ? Math.max(a, b) : -1;
            }
            case IMAX: {
                long a = toNat(l.imaxLhs());
                long b = toNat(l.imaxRhs());
                if (a >= 0 && b >= 0) return b == 0 ? 0 : Math.max(a, b);
                return -1;
            }
            case PARAM: return -1;
            default: return -1;
        }
    }

    public static Level fromNat(long n) {
        Level result = ZERO_LEVEL;
        for (long i = 0; i < n; i++) result = succ(result);
        return result;
    }

    // --- Instantiate ---

    public static Level instantiate(Level l, HashMap<Object, Level> subst) {
        switch (l.tag) {
            case ZERO: return ZERO_LEVEL;
            case SUCC: {
                Level inner = instantiate(l.succPred(), subst);
                return (inner == l.succPred()) ? l : succ(inner);
            }
            case MAX: {
                Level lhs = instantiate(l.maxLhs(), subst);
                Level rhs = instantiate(l.maxRhs(), subst);
                return (lhs == l.maxLhs() && rhs == l.maxRhs()) ? l : max(lhs, rhs);
            }
            case IMAX: {
                Level lhs = instantiate(l.imaxLhs(), subst);
                Level rhs = instantiate(l.imaxRhs(), subst);
                return (lhs == l.imaxLhs() && rhs == l.imaxRhs()) ? l : imax(lhs, rhs);
            }
            case PARAM: {
                Level mapped = subst.get(l.paramName());
                return mapped != null ? mapped : l;
            }
            default: return l;
        }
    }

    // --- Simplify ---

    public static Level simplify(Level l) {
        switch (l.tag) {
            case ZERO: return ZERO_LEVEL;
            case SUCC: {
                Level inner = simplify(l.succPred());
                if (inner.tag == MAX) {
                    return simplify(max(succ(inner.maxLhs()), succ(inner.maxRhs())));
                }
                return succ(inner);
            }
            case MAX: {
                // Full normalization following Lean 4's normalize (level.cpp:453-498).
                // Flatten max tree, sort components, remove duplicates, and subsume
                // explicit constants when a parametric component has higher offset.
                java.util.ArrayList<Level> components = new java.util.ArrayList<>();
                collectMaxComponents(l, components);
                // Simplify each component
                for (int i = 0; i < components.size(); i++)
                    components.set(i, simplify(components.get(i)));
                // Re-flatten after simplification (simplify may produce new max nodes)
                java.util.ArrayList<Level> flat = new java.util.ArrayList<>();
                for (Level c : components) {
                    if (c.tag == MAX) { collectMaxComponents(c, flat); }
                    else flat.add(c);
                }
                components = flat;
                // Sort by (kind, name, offset) for canonical form
                components.sort((x, y) -> levelNormCompare(x, y));
                // Subsume explicit constants and remove duplicates
                java.util.ArrayList<Level> result = new java.util.ArrayList<>();
                int idx = 0;
                // Handle leading explicit (concrete) levels
                if (idx < components.size() && isExplicit(components.get(idx))) {
                    // Find the largest explicit
                    while (idx + 1 < components.size() && isExplicit(components.get(idx + 1)))
                        idx++;
                    long explicitK = getOffsetVal(components.get(idx));
                    // Check if any non-explicit component has offset ≥ explicitK
                    boolean subsumed = false;
                    for (int j = idx + 1; j < components.size(); j++) {
                        if (getOffsetVal(components.get(j)) >= explicitK) {
                            subsumed = true;
                            break;
                        }
                    }
                    if (!subsumed) {
                        result.add(components.get(idx));
                    }
                    idx++;
                }
                // Add remaining, removing duplicates (keep highest offset for same base)
                long[] prevOff = new long[1];
                Level prevBase = idx < components.size() ? getOffset(components.get(idx), prevOff) : null;
                if (idx < components.size()) result.add(components.get(idx));
                for (int i = idx + 1; i < components.size(); i++) {
                    long[] currOff = new long[1];
                    Level currBase = getOffset(components.get(i), currOff);
                    if (prevBase != null && prevBase.equals(currBase)) {
                        if (currOff[0] > prevOff[0]) {
                            result.set(result.size() - 1, components.get(i));
                            prevOff[0] = currOff[0];
                        }
                        // else skip (duplicate with lower offset)
                    } else {
                        result.add(components.get(i));
                        prevBase = currBase;
                        prevOff[0] = currOff[0];
                    }
                }
                // Build result
                if (result.isEmpty()) return ZERO_LEVEL;
                Level r = result.get(result.size() - 1);
                for (int i = result.size() - 2; i >= 0; i--)
                    r = max(result.get(i), r);
                return r;
            }
            case IMAX: {
                Level a = simplify(l.imaxLhs());
                Level b = simplify(l.imaxRhs());
                long na = toNat(a);
                if (b.tag == ZERO) return ZERO_LEVEL;
                if (isNeverZero(b)) return simplify(max(a, b));
                if (a.equals(b)) return a;
                if (na == 1) return b;
                return imax(a, b);
            }
            case PARAM: return l;
            default: return l;
        }
    }

    // --- Normalization helpers ---

    /** Flatten a max tree into a list of non-max components. */
    private static void collectMaxComponents(Level l, java.util.ArrayList<Level> out) {
        if (l.tag == MAX) {
            collectMaxComponents((Level) l.o0, out);
            collectMaxComponents((Level) l.o1, out);
        } else {
            out.add(l);
        }
    }

    /** Check if a level is a concrete number (zero or succ^k(zero)). */
    private static boolean isExplicit(Level l) {
        return toNat(l) >= 0;
    }

    /** Get the succ offset of a level. */
    private static long getOffsetVal(Level l) {
        long k = 0;
        while (l.tag == SUCC) { l = l.succPred(); k++; }
        return k;
    }

    /** Compare levels for normalization sort order.
     *  Follows Lean 4's is_norm_lt: sort by (kind of base, name, offset). */
    private static int levelNormCompare(Level a, Level b) {
        long[] oa = new long[1], ob = new long[1];
        Level ba = getOffset(a, oa);
        Level bb = getOffset(b, ob);
        if (!ba.equals(bb)) {
            // Sort by kind first (Zero < Succ < Max < IMax < Param)
            if (ba.tag != bb.tag) return Integer.compare(ba.tag, bb.tag);
            // Same kind: compare by structure
            if (ba.tag == PARAM) {
                return ba.o0.toString().compareTo(bb.o0.toString());
            }
            return Integer.compare(ba.hashCode(), bb.hashCode());
        }
        return Long.compare(oa[0], ob[0]);
    }

    // --- Level comparison (Lean 4 algorithm) ---

    /** Strip succs, return [base, offset]. offset stored in out[0]. */
    private static Level getOffset(Level l, long[] out) {
        long k = 0;
        while (l.tag == SUCC) {
            l = l.succPred();
            k++;
        }
        out[0] = k;
        return l;
    }

    /** Collect (base, offset) components by flattening max nodes. */
    private static void collectComponents(Level l, java.util.ArrayList<Object[]> acc) {
        Level s = simplify(l);
        if (s.tag == MAX) {
            collectComponents(s.maxLhs(), acc);
            collectComponents(s.maxRhs(), acc);
        } else {
            long[] out = new long[1];
            Level base = getOffset(s, out);
            acc.add(new Object[]{base, out[0]});
        }
    }

    /** Is there any component in comps >= [base, k]? */
    private static boolean anyGeq(Level base, long k, java.util.ArrayList<Object[]> comps) {
        for (Object[] comp : comps) {
            Level b2 = (Level) comp[0];
            long k2 = (long) comp[1];
            if (base.equals(b2)) {
                if (k <= k2) return true;
            } else if (base.tag == ZERO && k <= k2) {
                return true;
            } else if (b2.tag == MAX) {
                java.util.ArrayList<Object[]> sub = new java.util.ArrayList<>();
                collectComponents(b2.maxLhs(), sub);
                collectComponents(b2.maxRhs(), sub);
                if (anyGeq(base, k, sub)) return true;
            }
        }
        return false;
    }

    /** Check l1 <= l2 for simplified, imax-free levels. */
    private static boolean leqCore(Level l1, Level l2) {
        java.util.ArrayList<Object[]> c1 = new java.util.ArrayList<>();
        java.util.ArrayList<Object[]> c2 = new java.util.ArrayList<>();
        collectComponents(l1, c1);
        collectComponents(l2, c2);
        for (Object[] comp : c1) {
            if (!anyGeq((Level) comp[0], (long) comp[1], c2)) return false;
        }
        return true;
    }

    /**
     * Check if l1 <= l2 for all possible assignments of level parameters.
     */
    /**
     * Level inequality: l1 ≤ l2.
     * Following Lean 4's is_geq (level.cpp:508-526) with swapped args:
     * leq(l1, l2) = is_geq(l2, l1).
     *
     * Key imax semantics: imax(a,b) = 0 when b=0, max(a,b) when b>0.
     * For imax on right of ≤: l1 ≤ imax(a,b) requires l1 ≤ a AND l1 ≤ b
     *   (because imax(a,b) ≥ max(a,b) ≥ a and ≥ b when b>0, and = 0 when b=0)
     *   Wait — actually Lean says: is_geq(imax(a,b), l2) = is_geq(b, l2)
     *   i.e. for imax on left of ≥: only rhs matters.
     *   For imax on right of ≥: is_geq(l1, imax(a,b)) = is_geq(l1,a) && is_geq(l1,b)
     *
     * In our leq(l1, l2) = is_geq(l2, l1):
     *   imax on l1 (left of ≤ = right of ≥): leq(imax(a,b), l2) = is_geq(l2, imax(a,b))
     *     = is_geq(l2, a) && is_geq(l2, b) = leq(a, l2) && leq(b, l2)
     *   imax on l2 (right of ≤ = left of ≥): leq(l1, imax(a,b)) = is_geq(imax(a,b), l1)
     *     = is_geq(b, l1) = leq(l1, b)
     */
    /**
     * Level inequality: l1 ≤ l2.
     * Following Lean 4's Lean-native Level.geq (src/Lean/Level.lean:608-625).
     * Converted from is_geq(l2, l1) with the Lean-native fallback that handles
     * the case where max on left and imax on right need combined decomposition.
     */
    public static boolean leq(Level l1, Level l2) {
        return geqGo(simplify(l2), simplify(l1));
    }

    /**
     * Core of Level.geq following the Lean-native implementation.
     * go(u, v) checks u ≥ v (i.e., v ≤ u).
     */
    private static boolean geqGo(Level u, Level v) {
        if (u.equals(v)) return true;

        // Fallback: decompose v (the "smaller" side)
        // This is the key difference from the C++ is_geq_core: the fallback
        // handles imax on v even when u is max (combined decomposition).
        // k() in the Lean source.
        // We inline it as a lambda-like check at the end.

        // Match on (u, v) with priority order from the Lean source:
        if (v.tag == ZERO) return true;

        if (v.tag == MAX) {
            // max on right: u ≥ max(v1, v2) iff u ≥ v1 AND u ≥ v2
            return geqGo(u, v.maxLhs()) && geqGo(u, v.maxRhs());
        }

        if (u.tag == MAX) {
            // max on left: max(u1, u2) ≥ v if u1 ≥ v OR u2 ≥ v
            if (geqGo(u.maxLhs(), v) || geqGo(u.maxRhs(), v)) return true;
            // FALLBACK: try decomposing v (handles imax on v)
            return geqFallback(u, v);
        }

        if (u.tag == IMAX) {
            // imax on left: imax(u1, u2) ≥ v iff u2 ≥ v
            return geqGo(u.imaxRhs(), v);
        }

        if (u.tag == SUCC && v.tag == SUCC) {
            return geqGo(u.succPred(), v.succPred());
        }

        // Default fallback
        return geqFallback(u, v);
    }

    /**
     * Fallback for geqGo: decompose v (the right/smaller side).
     * Corresponds to `k()` in the Lean-native Level.geq.
     */
    private static boolean geqFallback(Level u, Level v) {
        if (v.tag == IMAX) {
            // imax on right: u ≥ imax(v1, v2) iff u ≥ v1 AND u ≥ v2
            return geqGo(u, v.imaxLhs()) && geqGo(u, v.imaxRhs());
        }
        // Structural comparison via offset
        long[] ou = new long[1], ov = new long[1];
        Level bu = getOffset(u, ou);
        Level bv = getOffset(v, ov);
        if (bu.equals(bv) || bv.tag == ZERO) {
            return ou[0] >= ov[0];
        }
        if (ou[0] == ov[0] && ou[0] > 0) {
            return geqGo(bu, bv);
        }
        return false;
    }

    /**
     * Definitional equality of levels: l1 = l2 iff l1 <= l2 and l2 <= l1.
     */
    public static boolean eq(Level l1, Level l2) {
        if (l1 == l2) return true;
        if (l1.equals(l2)) return true;
        Level s1 = simplify(l1);
        Level s2 = simplify(l2);
        if (s1.equals(s2)) return true;
        return leq(s1, s2) && leq(s2, s1);
    }

    // --- Semantic predicates (following Lean 4 level.cpp:160-172) ---

    /**
     * Returns true if level is provably zero for ALL universe parameter assignments.
     * Zero → true, Succ → false, Param → false,
     * Max(a,b) → isZero(a) && isZero(b),
     * IMax(a,b) → isZero(b) (imax(a,0) = 0 regardless of a).
     */
    public static boolean isZero(Level l) {
        l = simplify(l);
        switch (l.tag) {
            case ZERO: return true;
            case SUCC: return false;
            case PARAM: return false;
            case MAX: return isZero((Level) l.o0) && isZero((Level) l.o1);
            case IMAX: return isZero((Level) l.o1);
            default: return false;
        }
    }

    /**
     * Returns true if level is provably non-zero for ALL universe parameter assignments.
     * Zero → false, Succ → true, Param → false,
     * Max(a,b) → isNotZero(a) || isNotZero(b),
     * IMax(a,b) → isNotZero(b) (only b matters: imax(a,b)=b when b>0).
     */
    public static boolean isNotZero(Level l) {
        l = simplify(l);
        switch (l.tag) {
            case ZERO: return false;
            case SUCC: return true;
            case PARAM: return false;
            case MAX: return isNotZero((Level) l.o0) || isNotZero((Level) l.o1);
            case IMAX: return isNotZero((Level) l.o1);
            default: return false;
        }
    }

    // --- Equality and hashing ---

    @Override
    public int hashCode() { return hash; }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Level)) return false;
        Level o = (Level) obj;
        if (tag != o.tag || hash != o.hash) return false;
        switch (tag) {
            case ZERO: return true;
            case SUCC: return o0.equals(o.o0);
            case MAX: return o0.equals(o.o0) && o1.equals(o.o1);
            case IMAX: return o0.equals(o.o0) && o1.equals(o.o1);
            case PARAM: return o0.equals(o.o0);
            default: return false;
        }
    }

    // --- Display ---

    @Override
    public String toString() {
        switch (tag) {
            case ZERO: return "0";
            case SUCC: {
                Level base = this;
                long n = 0;
                while (base.tag == SUCC) { base = base.succPred(); n++; }
                if (base.tag == ZERO) return Long.toString(n);
                return "(" + base + " + " + n + ")";
            }
            case MAX: return "(max " + o0 + " " + o1 + ")";
            case IMAX: return "(imax " + o0 + " " + o1 + ")";
            case PARAM: return o0.toString();
            default: return "?level";
        }
    }
}
