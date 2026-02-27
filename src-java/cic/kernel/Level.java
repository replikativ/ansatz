// Copyright (c) 2026 Simmis GmbH. All rights reserved.
// CIC kernel — Universe levels with algebra and comparison.

package cic.kernel;

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
                Level a = simplify(l.maxLhs());
                Level b = simplify(l.maxRhs());
                long na = toNat(a);
                long nb = toNat(b);
                if (na >= 0 && nb >= 0) return fromNat(Math.max(na, nb));
                if (a.equals(b)) return a;
                if (na == 0) return b;
                if (nb == 0) return a;
                return max(a, b);
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
    public static boolean leq(Level l1, Level l2) {
        Level s1 = simplify(l1);
        Level s2 = simplify(l2);

        if (s1.equals(s2)) return true;
        if (s1.tag == ZERO) return true;
        if (s2.tag == ZERO && isNeverZero(s1)) return false;

        // imax on the left
        if (s1.tag == IMAX) {
            Level a = s1.imaxLhs(), b = s1.imaxRhs();
            if (b.tag == ZERO) return true;
            if (isNeverZero(b)) return leq(simplify(max(a, b)), s2);
            return leq(simplify(max(a, b)), s2);
        }

        // imax on the right
        if (s2.tag == IMAX) {
            Level a = s2.imaxLhs(), b = s2.imaxRhs();
            if (b.tag == ZERO) return leq(s1, ZERO_LEVEL);
            if (isNeverZero(b)) return leq(s1, simplify(max(a, b)));
            return leq(s1, simplify(max(a, b))) || s1.equals(s2);
        }

        // max on the left
        if (s1.tag == MAX) {
            return leq(s1.maxLhs(), s2) && leq(s1.maxRhs(), s2);
        }

        // max on the right
        if (s2.tag == MAX) {
            return leq(s1, s2.maxLhs()) || leq(s1, s2.maxRhs()) || leqCore(s1, s2);
        }

        return leqCore(s1, s2);
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
