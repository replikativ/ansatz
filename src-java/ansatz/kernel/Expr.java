// Ansatz kernel — compact Java expression type.
// Replaces PersistentVector-based expressions for ~64% memory reduction.

package ansatz.kernel;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Objects;

/**
 * Compact, immutable expression node for the Calculus of Inductive Constructions.
 *
 * <p>Single final class with byte tag + packed long metadata + named final fields.
 * JIT can fully inline field access via getfield bytecode (no invokeinterface overhead).
 *
 * <p>Memory layout: 16 (header) + 8 (tag padded) + 8 (data) + 32 (4 refs) + 8 (longVal) = ~72 bytes.
 * Compared to ~200 bytes for PersistentVector + metadata map.
 *
 * <p>Packed {@code data} long layout:
 * <ul>
 *   <li>bits 0-19:  bvarRange (20 bits, max ~1M)
 *   <li>bits 20-51: hash (32 bits)
 *   <li>bit 62:     hasFVar
 *   <li>bit 63:     hasLevelParam (sign bit)
 * </ul>
 */
public final class Expr {

    // Tag constants
    public static final byte BVAR = 0;
    public static final byte SORT = 1;
    public static final byte CONST = 2;
    public static final byte APP = 3;
    public static final byte LAM = 4;
    public static final byte FORALL = 5;
    public static final byte LET = 6;
    public static final byte LIT_NAT = 7;
    public static final byte LIT_STR = 8;
    public static final byte MDATA = 9;
    public static final byte PROJ = 10;
    public static final byte FVAR = 11;
    public static final byte MVAR = 12;

    // Bit masks for packed data
    private static final long BVAR_RANGE_MASK = 0xFFFFF; // 20 bits
    private static final long HASH_MASK = 0xFFFFFFFFL;   // 32 bits
    private static final int HASH_SHIFT = 20;
    private static final long HAS_FVAR_BIT = 1L << 62;
    // bit 63 = sign bit, used for hasLevelParam

    public final byte tag;
    public final long data;     // packed: bvarRange | hash | hasFVar | hasLevelParam
    public final Object o0;     // tag-dependent: sub-expr, name, BigInteger, String, etc.
    public final Object o1;     // tag-dependent: sub-expr, levels, etc.
    public final Object o2;     // tag-dependent: body, etc.
    public final Object o3;     // tag-dependent: binderInfo, body, etc.
    public final long longVal;  // bvar idx, fvar id, proj idx

    /**
     * Expression store ID. If >= 0, this expression was resolved from an ExprStore
     * and two Expr objects with the same storeId are structurally equal.
     * This provides Lean 4's is_eqp semantics: identity checks via integer comparison.
     * -1 means the expression was created during reduction (not from the store).
     */
    public int storeId = -1;

    private Expr(byte tag, long data, Object o0, Object o1, Object o2, Object o3, long longVal) {
        this.tag = tag;
        this.data = data;
        this.o0 = o0;
        this.o1 = o1;
        this.o2 = o2;
        this.o3 = o3;
        this.longVal = longVal;
    }

    /**
     * Pointer-equality check matching Lean 4's is_eqp.
     * Returns true if both expressions are the same Java object, or if both
     * originate from the same ExprStore entry (same storeId >= 0).
     */
    public boolean isEqp(Expr other) {
        return this == other || (this.storeId >= 0 && this.storeId == other.storeId);
    }

    // ---- Hash-consing intern table ----
    // Thread-local intern table for expression deduplication during type checking.
    // When enabled, factory methods (app, lam, forall, etc.) return existing
    // structurally-equal expressions, making pointer equality (isEqp / ==) succeed
    // for identical intermediate results. This matches Lean 4's C++ allocator behavior.
    private static final ThreadLocal<HashMap<Expr, Expr>> internTable = new ThreadLocal<>();
    /** Enable hash-consing for the current thread. Call disableIntern() when done. */
    public static void enableIntern() {
        internTable.set(new HashMap<>(16384));
    }

    /** Disable hash-consing and free the intern table.
     *  The table is per-declaration (created in checkConstant, freed after).
     *  No size limit — grows as needed, then GC'd on disableIntern(). */
    public static void disableIntern() {
        internTable.remove();
    }

    /** Seed the intern table with entries from shareCommon's cache.
     *  Ensures proof sub-expressions are pointer-identical to reduction-created ones. */
    public static void seedIntern(java.util.HashMap<Expr, Expr> scCache) {
        HashMap<Expr, Expr> table = internTable.get();
        if (table != null) table.putAll(scCache);
    }

    /** Re-intern an expression from outside the intern table (e.g., ENV values).
     *  If already in the table, returns the canonical pointer. If not, adds it.
     *  Just the top node — for deep re-interning use deepReIntern. */
    public static Expr reIntern(Expr e) {
        HashMap<Expr, Expr> table = internTable.get();
        if (table == null) return e;
        Expr existing = table.putIfAbsent(e, e);
        return existing != null ? existing : e;
    }

    /** Deeply re-intern an expression tree. Rebuilds the tree bottom-up using
     *  the interned factory methods, ensuring ALL sub-expressions are in the
     *  intern table. Used for ENV definition values entering the kernel.
     *  Results are cached per identity to avoid redundant work on DAG-shared sub-trees. */
    public static Expr deepReIntern(Expr e) {
        HashMap<Expr, Expr> table = internTable.get();
        if (table == null) return e;
        // Quick check: if already in the table, return canonical form immediately.
        // After the CONST fix, structural-hash + structural-equals means this lookup
        // correctly finds the canonical pointer even for fresh Object[] level arrays.
        Expr existing = table.get(e);
        if (existing != null) return existing;
        return deepReInternGo(e, new IdentityHashMap<>(256));
    }

    private static Expr deepReInternGo(Expr e, IdentityHashMap<Expr, Expr> visited) {
        Expr cached = visited.get(e);
        if (cached != null) return cached;
        // If already in intern table, use canonical version
        HashMap<Expr, Expr> table = internTable.get();
        if (table != null) {
            Expr existing = table.get(e);
            if (existing != null) { visited.put(e, existing); return existing; }
        }
        Expr result;
        switch (e.tag) {
            case BVAR: result = bvar(e.longVal); break;
            case SORT: result = sort(e.o0, e.hasLevelParam()); break;
            case CONST: result = mkConst(e.o0, e.o1, e.hasLevelParam()); break;
            case FVAR: result = fvar(e.longVal); break;
            case MVAR: result = mvar(e.longVal); break;
            case LIT_NAT: result = litNat(e.o0); break;
            case LIT_STR: result = litStr((String) e.o0); break;
            case APP: {
                Expr fn = deepReInternGo((Expr) e.o0, visited);
                Expr arg = deepReInternGo((Expr) e.o1, visited);
                result = app(fn, arg);
                break;
            }
            case LAM: {
                Expr type = deepReInternGo((Expr) e.o1, visited);
                Expr body = deepReInternGo((Expr) e.o2, visited);
                result = lam(e.o0, type, body, e.o3);
                break;
            }
            case FORALL: {
                Expr type = deepReInternGo((Expr) e.o1, visited);
                Expr body = deepReInternGo((Expr) e.o2, visited);
                result = forall(e.o0, type, body, e.o3);
                break;
            }
            case LET: {
                // LET is rare in kernel expressions; re-intern top node only
                result = reIntern(e);
                break;
            }
            case PROJ: {
                Expr struct = deepReInternGo((Expr) e.o1, visited);
                result = proj(e.o0, e.longVal, struct);
                break;
            }
            case MDATA: {
                Expr inner = deepReInternGo((Expr) e.o1, visited);
                result = mdata(e.o0, inner);
                break;
            }
            default: result = e;
        }
        visited.put(e, result);
        return result;
    }

    /** Intern an expression: return canonical instance if one exists. */
    private static Expr intern(Expr e) {
        HashMap<Expr, Expr> table = internTable.get();
        if (table == null) return e;
        Expr existing = table.putIfAbsent(e, e);
        return existing != null ? existing : e;
    }

    // --- Packed data helpers ---

    private static long packData(long bvarRange, int hash, boolean hasFVar, boolean hasLevelParam) {
        return (bvarRange & BVAR_RANGE_MASK)
             | (((long) hash & HASH_MASK) << HASH_SHIFT)
             | (hasFVar ? HAS_FVAR_BIT : 0L)
             | (hasLevelParam ? Long.MIN_VALUE : 0L); // bit 63
    }

    // --- Metadata extraction ---

    /** Upper bound on loose de Bruijn indices. 0 means no loose bvars. */
    public long bvarRange() {
        return data & BVAR_RANGE_MASK;
    }

    /** Does this expression contain any free variable? */
    public boolean hasFVar() {
        return (data & HAS_FVAR_BIT) != 0;
    }

    /** Does this expression contain any universe level parameter? */
    public boolean hasLevelParam() {
        return data < 0; // bit 63 = sign bit
    }

    // --- Hash and equality ---
    //
    // Structural equality and hash. Used by HashMap-based caches in TypeChecker
    // and Reducer. After shareCommon(), identity-equal sub-expressions make
    // these comparisons fast (the `this == obj` check fires immediately).
    //
    // The structuralHash() method is also exposed separately for use in factory
    // methods that need to compute the hash during construction.

    @Override
    public int hashCode() {
        return (int) ((data >>> HASH_SHIFT) & HASH_MASK);
    }

    /** Alias for hashCode() — makes intent explicit in factory methods. */
    public int structuralHash() {
        return hashCode();
    }

    /**
     * Structural hash for a CONST's level list, consistent across Object[], List, and
     * IPersistentVector representations.  After level normalization, levels may be stored
     * as a fresh Object[] whose identity hash differs from a structurally-equal List —
     * causing the intern table to miss.  This helper ensures consistent hashing.
     */
    static int levelsHashCode(Object levels) {
        if (levels == null) return 0;
        if (levels instanceof Object[]) {
            Object[] arr = (Object[]) levels;
            int h = 1;
            for (Object e : arr) h = 31 * h + (e == null ? 0 : e.hashCode());
            return h;
        }
        // java.util.List (Arrays.asList, etc.) and IPersistentVector both have
        // structural hashCode matching the formula above.
        return levels.hashCode();
    }

    /**
     * Structural equality for CONST level lists, consistent across representation types.
     */
    static boolean levelsEquals(Object a, Object b) {
        if (a == b) return true;
        if (a == null || b == null) return false;
        if (a instanceof Object[] && b instanceof Object[]) {
            Object[] aa = (Object[]) a, ab = (Object[]) b;
            if (aa.length != ab.length) return false;
            for (int i = 0; i < aa.length; i++) if (!aa[i].equals(ab[i])) return false;
            return true;
        }
        if (a instanceof Object[]) return mixedLevelsEquals((Object[]) a, b);
        if (b instanceof Object[]) return mixedLevelsEquals((Object[]) b, a);
        return Objects.equals(a, b); // List / IPersistentVector structural equals
    }

    private static boolean mixedLevelsEquals(Object[] arr, Object other) {
        if (other instanceof java.util.List) {
            java.util.List<?> lst = (java.util.List<?>) other;
            if (lst.size() != arr.length) return false;
            for (int i = 0; i < arr.length; i++) if (!arr[i].equals(lst.get(i))) return false;
            return true;
        }
        if (other instanceof clojure.lang.IPersistentVector) {
            clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) other;
            if (v.count() != arr.length) return false;
            for (int i = 0; i < arr.length; i++) if (!arr[i].equals(v.nth(i))) return false;
            return true;
        }
        return false;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Expr)) return false;
        Expr o = (Expr) obj;
        if (tag != o.tag) return false;
        // Fast reject: if packed data differs (hash + bvarRange + flags), almost certainly not equal.
        if (data != o.data) return false;
        switch (tag) {
            case BVAR:    return longVal == o.longVal;
            case SORT:    return Objects.equals(o0, o.o0);
            case CONST:   return Objects.equals(o0, o.o0) && levelsEquals(o1, o.o1);
            case APP:     return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1);
            case LAM:     return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1)
                              && Objects.equals(o2, o.o2) && Objects.equals(o3, o.o3);
            case FORALL:  return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1)
                              && Objects.equals(o2, o.o2) && Objects.equals(o3, o.o3);
            case LET:     return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1)
                              && Objects.equals(o2, o.o2) && Objects.equals(o3, o.o3);
            case LIT_NAT: return Objects.equals(o0, o.o0);
            case LIT_STR: return Objects.equals(o0, o.o0);
            case MDATA:   return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1);
            case PROJ:    return Objects.equals(o0, o.o0) && Objects.equals(o1, o.o1) && longVal == o.longVal;
            case FVAR:    return longVal == o.longVal;
            case MVAR:    return longVal == o.longVal;
            default:      return false;
        }
    }

    @Override
    public String toString() {
        switch (tag) {
            case BVAR:    return "(bvar " + longVal + ")";
            case SORT:    return "(sort " + o0 + ")";
            case CONST:   return "(const " + o0 + " " + o1 + ")";
            case APP:     return "(app " + o0 + " " + o1 + ")";
            case LAM:     return "(lam " + o0 + " " + o1 + " " + o2 + " " + o3 + ")";
            case FORALL:  return "(forall " + o0 + " " + o1 + " " + o2 + " " + o3 + ")";
            case LET:     return "(let " + o0 + " " + o1 + " " + o2 + " " + o3 + ")";
            case LIT_NAT: return "(lit-nat " + o0 + ")";
            case LIT_STR: return "(lit-str " + o0 + ")";
            case MDATA:   return "(mdata " + o0 + " " + o1 + ")";
            case PROJ:    return "(proj " + o0 + " " + longVal + " " + o1 + ")";
            case FVAR:    return "(fvar " + longVal + ")";
            case MVAR:    return "(mvar " + longVal + ")";
            default:      return "(unknown-expr)";
        }
    }

    // --- Static factory methods ---
    // Each computes bvarRange, hasFVar, hasLevelParam metadata compositionally,
    // then packs into the data long with a hash.

    /** Bound variable (de Bruijn index). */
    public static Expr bvar(long idx) {
        int h = Long.hashCode(idx) * 31 + BVAR;
        long d = packData(idx + 1, h, false, false);
        return intern(new Expr(BVAR, d, null, null, null, null, idx));
    }

    /** Normalize all universe levels in an expression tree.
     *  Ensures equivalent levels produce structurally identical Level objects,
     *  so that Expr pointer equality (via intern table) works for expressions
     *  with equivalent-but-differently-structured levels. */
    public static Expr normalizeExprLevels(Expr e) {
        return normalizeExprLevelsGo(e, new IdentityHashMap<>(256));
    }

    private static Expr normalizeExprLevelsGo(Expr e, IdentityHashMap<Expr, Expr> visited) {
        Expr cached = visited.get(e);
        if (cached != null) return cached;
        Expr result;
        switch (e.tag) {
            case SORT: {
                Level l = (Level) e.o0;
                Level norm = Level.simplify(l);
                result = (norm == l) ? e : sort(norm, e.hasLevelParam());
                break;
            }
            case CONST: {
                Object levels = e.o1;
                boolean changed = false;
                if (levels instanceof Object[]) {
                    Object[] arr = (Object[]) levels;
                    Object[] norm = null;
                    for (int i = 0; i < arr.length; i++) {
                        Level simplified = Level.simplify((Level) arr[i]);
                        if (simplified != arr[i]) {
                            if (norm == null) norm = arr.clone();
                            norm[i] = simplified;
                            changed = true;
                        }
                    }
                    if (changed) {
                        result = mkConst(e.o0, norm, e.hasLevelParam());
                    } else {
                        result = e;
                    }
                } else if (levels instanceof clojure.lang.IPersistentVector) {
                    clojure.lang.IPersistentVector v = (clojure.lang.IPersistentVector) levels;
                    Object[] norm = new Object[v.count()];
                    for (int i = 0; i < v.count(); i++) {
                        Level simplified = Level.simplify((Level) v.nth(i));
                        norm[i] = simplified;
                        if (simplified != v.nth(i)) changed = true;
                    }
                    result = changed ? mkConst(e.o0, norm, e.hasLevelParam()) : e;
                } else {
                    result = e;
                }
                break;
            }
            case APP: {
                Expr fn = normalizeExprLevelsGo((Expr) e.o0, visited);
                Expr arg = normalizeExprLevelsGo((Expr) e.o1, visited);
                result = (fn == e.o0 && arg == e.o1) ? e : app(fn, arg);
                break;
            }
            case LAM: {
                Expr type = normalizeExprLevelsGo((Expr) e.o1, visited);
                Expr body = normalizeExprLevelsGo((Expr) e.o2, visited);
                result = (type == e.o1 && body == e.o2) ? e : lam(e.o0, type, body, e.o3);
                break;
            }
            case FORALL: {
                Expr type = normalizeExprLevelsGo((Expr) e.o1, visited);
                Expr body = normalizeExprLevelsGo((Expr) e.o2, visited);
                result = (type == e.o1 && body == e.o2) ? e : forall(e.o0, type, body, e.o3);
                break;
            }
            case PROJ: {
                Expr struct = normalizeExprLevelsGo((Expr) e.o1, visited);
                result = (struct == e.o1) ? e : proj(e.o0, e.longVal, struct);
                break;
            }
            default:
                result = e;
        }
        visited.put(e, result);
        return result;
    }

    /** Sort (universe). Prop = sort(zero), Type u = sort(succ u). */
    public static Expr sort(Object level, boolean levelHasParam) {
        int h = Objects.hashCode(level) * 31 + SORT;
        long d = packData(0, h, false, levelHasParam);
        return intern(new Expr(SORT, d, level, null, null, null, 0));
    }

    /** Reference to a global constant with universe level arguments. */
    public static Expr mkConst(Object name, Object levels, boolean levelsHaveParam) {
        // Use structural hash for levels so CONSTs with equal level contents (but
        // different Object[] instances — common after normalization) hash to the same
        // bucket and are recognized as equal by the intern table.
        int h = (Objects.hashCode(name) * 31 + levelsHashCode(levels)) * 31 + CONST;
        long d = packData(0, h, false, levelsHaveParam);
        return intern(new Expr(CONST, d, name, levels, null, null, 0));
    }

    /** Function application (curried). */
    public static Expr app(Expr fn, Expr arg) {
        long br = Math.max(fn.bvarRange(), arg.bvarRange());
        boolean fv = fn.hasFVar() || arg.hasFVar();
        boolean lp = fn.hasLevelParam() || arg.hasLevelParam();
        int h = (fn.structuralHash() * 31 + arg.structuralHash()) * 31 + APP;
        long d = packData(br, h, fv, lp);
        return intern(new Expr(APP, d, fn, arg, null, null, 0));
    }

    /** Lambda abstraction. */
    public static Expr lam(Object name, Expr type, Expr body, Object binderInfo) {
        long bodyRange = body.bvarRange();
        long br = Math.max(type.bvarRange(), bodyRange > 0 ? bodyRange - 1 : 0);
        boolean fv = type.hasFVar() || body.hasFVar();
        boolean lp = type.hasLevelParam() || body.hasLevelParam();
        int h = (Objects.hashCode(name) * 31 + type.structuralHash() * 17 + body.structuralHash()) * 31 + LAM;
        long d = packData(br, h, fv, lp);
        return intern(new Expr(LAM, d, name, type, body, binderInfo, 0));
    }

    /** Pi type / dependent function type. */
    public static Expr forall(Object name, Expr type, Expr body, Object binderInfo) {
        long bodyRange = body.bvarRange();
        long br = Math.max(type.bvarRange(), bodyRange > 0 ? bodyRange - 1 : 0);
        boolean fv = type.hasFVar() || body.hasFVar();
        boolean lp = type.hasLevelParam() || body.hasLevelParam();
        int h = (Objects.hashCode(name) * 31 + type.structuralHash() * 17 + body.structuralHash()) * 31 + FORALL;
        long d = packData(br, h, fv, lp);
        return intern(new Expr(FORALL, d, name, type, body, binderInfo, 0));
    }

    /** Let binding with type annotation. */
    public static Expr mkLet(Object name, Expr type, Expr value, Expr body) {
        long bodyRange = body.bvarRange();
        long br = Math.max(Math.max(type.bvarRange(), value.bvarRange()),
                           bodyRange > 0 ? bodyRange - 1 : 0);
        boolean fv = type.hasFVar() || value.hasFVar() || body.hasFVar();
        boolean lp = type.hasLevelParam() || value.hasLevelParam() || body.hasLevelParam();
        int h = (Objects.hashCode(name) * 31 + type.structuralHash() * 17
                + value.structuralHash() * 13 + body.structuralHash()) * 31 + LET;
        long d = packData(br, h, fv, lp);
        return intern(new Expr(LET, d, name, type, value, body, 0));
    }

    /** Natural number literal. Always stores value as BigInteger for consistent equality. */
    public static Expr litNat(Object n) {
        BigInteger val;
        if (n instanceof BigInteger) {
            val = (BigInteger) n;
        } else if (n instanceof clojure.lang.BigInt) {
            val = ((clojure.lang.BigInt) n).toBigInteger();
        } else if (n instanceof Number) {
            val = BigInteger.valueOf(((Number) n).longValue());
        } else {
            val = new BigInteger(n.toString());
        }
        int h = val.hashCode() * 31 + LIT_NAT;
        long d = packData(0, h, false, false);
        return intern(new Expr(LIT_NAT, d, val, null, null, null, 0));
    }

    /** String literal. */
    public static Expr litStr(String s) {
        int h = s.hashCode() * 31 + LIT_STR;
        long d = packData(0, h, false, false);
        return intern(new Expr(LIT_STR, d, s, null, null, null, 0));
    }

    /** Metadata annotation (definitionally transparent). */
    public static Expr mdata(Object data, Expr expr) {
        int h = (Objects.hashCode(data) * 31 + expr.structuralHash()) * 31 + MDATA;
        long dd = packData(expr.bvarRange(), h, expr.hasFVar(), expr.hasLevelParam());
        return intern(new Expr(MDATA, dd, data, expr, null, null, 0));
    }

    /** Structure projection. */
    public static Expr proj(Object typeName, long idx, Expr struct) {
        int h = (Objects.hashCode(typeName) * 31 + Long.hashCode(idx) * 17
                + struct.structuralHash()) * 31 + PROJ;
        long d = packData(struct.bvarRange(), h, struct.hasFVar(), struct.hasLevelParam());
        return intern(new Expr(PROJ, d, typeName, struct, null, null, idx));
    }

    /** Free variable with unique numeric id. Interned for pointer sharing. */
    public static Expr fvar(long id) {
        int h = Long.hashCode(id) * 31 + FVAR;
        long d = packData(0, h, true, false);
        return intern(new Expr(FVAR, d, null, null, null, null, id));
    }

    /** Metavariable with unique numeric id. Interned for pointer sharing.
     *  NOT affected by abstract1 (HAS_FVAR_BIT is false). */
    public static Expr mvar(long id) {
        int h = Long.hashCode(id) * 31 + MVAR;
        // MVAR does NOT set HAS_FVAR_BIT — this ensures abstract1 skips it
        long d = packData(0, h, false, false);
        return intern(new Expr(MVAR, d, null, null, null, null, id));
    }

    /**
     * Share common sub-expressions (hash consing).
     * Walks the expression tree bottom-up, deduplicating structurally equal sub-expressions
     * so they share identity. This matches Lean 4's sharecommon_persistent_fn.
     * After sharing, identity-based caches (IdentityHashMap) and pointer equality (==)
     * become much more effective.
     */
    public static Expr shareCommon(Expr e) {
        java.util.HashMap<Expr, Expr> cache = new java.util.HashMap<>(4096);
        java.util.IdentityHashMap<Expr, Expr> visited = new java.util.IdentityHashMap<>(4096);
        return shareCommonGo(e, cache, visited);
    }

    /**
     * Share common sub-expressions across multiple expression trees.
     * Call with the same cache/visited maps to share identity between
     * e.g. a declaration's type and value.
     */
    public static Expr shareCommon(Expr e, java.util.HashMap<Expr, Expr> cache,
                                    java.util.IdentityHashMap<Expr, Expr> visited) {
        return shareCommonGo(e, cache, visited);
    }

    private static Expr shareCommonGo(Expr e, java.util.HashMap<Expr, Expr> cache,
                                       java.util.IdentityHashMap<Expr, Expr> visited) {
        // Fast path: already visited this exact object
        Expr v = visited.get(e);
        if (v != null) return v;

        Expr result;
        switch (e.tag) {
            case BVAR: case SORT: case CONST: case LIT_NAT: case LIT_STR: case FVAR: case MVAR:
                result = e;
                break;
            case APP: {
                Expr fn = shareCommonGo((Expr) e.o0, cache, visited);
                Expr arg = shareCommonGo((Expr) e.o1, cache, visited);
                result = (fn == e.o0 && arg == e.o1) ? e : app(fn, arg);
                break;
            }
            case LAM: {
                Expr type = shareCommonGo((Expr) e.o1, cache, visited);
                Expr body = shareCommonGo((Expr) e.o2, cache, visited);
                result = (type == e.o1 && body == e.o2) ? e : lam(e.o0, type, body, e.o3);
                break;
            }
            case FORALL: {
                Expr type = shareCommonGo((Expr) e.o1, cache, visited);
                Expr body = shareCommonGo((Expr) e.o2, cache, visited);
                result = (type == e.o1 && body == e.o2) ? e : forall(e.o0, type, body, e.o3);
                break;
            }
            case LET: {
                Expr type = shareCommonGo((Expr) e.o1, cache, visited);
                Expr value = shareCommonGo((Expr) e.o2, cache, visited);
                Expr body = shareCommonGo((Expr) e.o3, cache, visited);
                result = (type == e.o1 && value == e.o2 && body == e.o3) ? e : mkLet(e.o0, type, value, body);
                break;
            }
            case MDATA: {
                Expr inner = shareCommonGo((Expr) e.o1, cache, visited);
                result = (inner == e.o1) ? e : mdata(e.o0, inner);
                break;
            }
            case PROJ: {
                Expr struct = shareCommonGo((Expr) e.o1, cache, visited);
                result = (struct == e.o1) ? e : proj(e.o0, e.longVal, struct);
                break;
            }
            default:
                result = e;
        }
        // Propagate storeId to rebuilt expressions
        if (result != e && result.storeId < 0 && e.storeId >= 0) {
            result.storeId = e.storeId;
        }
        // Intern: if we've seen a structurally equal expression, reuse it
        Expr existing = cache.putIfAbsent(result, result);
        Expr canonical = existing != null ? existing : result;
        // If canonical has no storeId but the original did, propagate it
        if (canonical.storeId < 0 && e.storeId >= 0) {
            canonical.storeId = e.storeId;
        }
        visited.put(e, canonical);
        return canonical;
    }
}
