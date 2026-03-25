// Ansatz kernel — Interned hierarchical names for fast identity comparison.

package ansatz.kernel;

import java.util.concurrent.ConcurrentHashMap;

/**
 * Interned hierarchical name, matching Lean's Name type.
 *
 * <p>Names are immutable and interned: after interning, identity comparison (==)
 * is sufficient for equality. This replaces Clojure's structural vector equality
 * (~80ns) with pointer comparison (~2ns).
 *
 * <p>Variants:
 * <ul>
 *   <li>ANONYMOUS — the root/empty name (singleton)
 *   <li>STR — parent.string (e.g., Nat.add)
 *   <li>NUM — parent.number (e.g., _uniq.42)
 * </ul>
 */
public final class Name {

    public static final byte ANONYMOUS = 0;
    public static final byte STR = 1;
    public static final byte NUM = 2;

    public final byte tag;
    public final int hash;
    public final Name prefix;  // null for anonymous
    public final String str;   // for STR
    public final long num;     // for NUM

    private Name(byte tag, int hash, Name prefix, String str, long num) {
        this.tag = tag;
        this.hash = hash;
        this.prefix = prefix;
        this.str = str;
        this.num = num;
    }

    // --- Singleton anonymous ---

    public static final Name ANONYMOUS_NAME = new Name(ANONYMOUS, 0, null, null, 0);

    // --- Intern table ---

    private static final ConcurrentHashMap<Name, Name> internTable =
        new ConcurrentHashMap<>(65536);

    static {
        internTable.put(ANONYMOUS_NAME, ANONYMOUS_NAME);
    }

    private static Name intern(Name n) {
        Name existing = internTable.putIfAbsent(n, n);
        return existing != null ? existing : n;
    }

    // --- Factories (always return interned instances) ---

    public static Name mkStr(Name prefix, String s) {
        int h = (prefix != null ? prefix.hash : 0) * 31 + s.hashCode();
        Name n = new Name(STR, h, prefix, s, 0);
        return intern(n);
    }

    public static Name mkNum(Name prefix, long i) {
        int h = (prefix != null ? prefix.hash : 0) * 31 + Long.hashCode(i);
        Name n = new Name(NUM, h, prefix, null, i);
        return intern(n);
    }

    /**
     * Parse a dot-separated string into a Name.
     * E.g., "Nat.add" -> mkStr(mkStr(ANONYMOUS, "Nat"), "add")
     * Numeric parts are created with mkNum (e.g., "_uniq.42" -> mkNum(mkStr(ANONYMOUS, "_uniq"), 42)).
     */
    public static Name fromString(String s) {
        Name result = ANONYMOUS_NAME;
        for (String part : s.split("\\.", -1)) {
            if (!part.isEmpty() && isNumeric(part)) {
                result = mkNum(result, Long.parseLong(part));
            } else {
                result = mkStr(result, part);
            }
        }
        return result;
    }

    private static boolean isNumeric(String s) {
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c < '0' || c > '9') return false;
        }
        return true;
    }

    // --- Pre-interned well-known names ---

    public static final Name NAT = fromString("Nat");
    public static final Name NAT_ZERO = fromString("Nat.zero");
    public static final Name NAT_SUCC = fromString("Nat.succ");
    public static final Name NAT_ADD = fromString("Nat.add");
    public static final Name NAT_SUB = fromString("Nat.sub");
    public static final Name NAT_MUL = fromString("Nat.mul");
    public static final Name NAT_DIV = fromString("Nat.div");
    public static final Name NAT_MOD = fromString("Nat.mod");
    public static final Name NAT_POW = fromString("Nat.pow");
    public static final Name NAT_GCD = fromString("Nat.gcd");
    public static final Name NAT_BEQ = fromString("Nat.beq");
    public static final Name NAT_BLE = fromString("Nat.ble");
    public static final Name NAT_LAND = fromString("Nat.land");
    public static final Name NAT_LOR = fromString("Nat.lor");
    public static final Name NAT_XOR = fromString("Nat.xor");
    public static final Name NAT_SHIFT_LEFT = fromString("Nat.shiftLeft");
    public static final Name NAT_SHIFT_RIGHT = fromString("Nat.shiftRight");
    public static final Name NAT_REC = fromString("Nat.rec");
    public static final Name NAT_DEC_EQ = fromString("Nat.decEq");
    public static final Name INST_DECIDABLE_EQ_NAT = fromString("instDecidableEqNat");

    // Decidable constructors and Eq
    public static final Name DECIDABLE_IS_TRUE = fromString("Decidable.isTrue");
    public static final Name DECIDABLE_IS_FALSE = fromString("Decidable.isFalse");
    public static final Name EQ_REFL = fromString("Eq.refl");
    public static final Name EQ = fromString("Eq");

    // Int operations (native reduction for performance)
    public static final Name INT_OF_NAT = fromString("Int.ofNat");
    public static final Name INT_NEG_SUCC = fromString("Int.negSucc");
    public static final Name INT_ADD = fromString("Int.add");
    public static final Name INT_SUB = fromString("Int.sub");
    public static final Name INT_MUL = fromString("Int.mul");
    public static final Name INT_NEG = fromString("Int.neg");
    public static final Name INT_NAT_ABS = fromString("Int.natAbs");
    public static final Name INT_EDIV = fromString("Int.ediv");
    public static final Name INT_EMOD = fromString("Int.emod");
    public static final Name INT_DEC_EQ = fromString("Int.decEq");

    public static final Name BOOL_TRUE = fromString("Bool.true");
    public static final Name BOOL_FALSE = fromString("Bool.false");
    public static final Name STRING = fromString("String");
    public static final Name STRING_MK = fromString("String.mk");
    public static final Name STRING_OF_LIST = fromString("String.ofList");
    public static final Name LIST_CONS = fromString("List.cons");
    public static final Name LIST_NIL = fromString("List.nil");
    public static final Name CHAR = fromString("Char");
    public static final Name CHAR_OF_NAT = fromString("Char.ofNat");

    public static final Name EAGER_REDUCE = fromString("eagerReduce");

    public static final Name QUOT = fromString("Quot");
    public static final Name QUOT_MK = fromString("Quot.mk");
    public static final Name QUOT_LIFT = fromString("Quot.lift");
    public static final Name QUOT_IND = fromString("Quot.ind");

    // --- Accessors ---

    public boolean isAnonymous() { return tag == ANONYMOUS; }
    public boolean isStr() { return tag == STR; }
    public boolean isNum() { return tag == NUM; }

    // --- Equality and hashing ---

    @Override
    public int hashCode() { return hash; }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Name)) return false;
        Name o = (Name) obj;
        if (tag != o.tag || hash != o.hash) return false;
        switch (tag) {
            case ANONYMOUS: return true;
            case STR: return str.equals(o.str) && eqPrefix(prefix, o.prefix);
            case NUM: return num == o.num && eqPrefix(prefix, o.prefix);
            default: return false;
        }
    }

    private static boolean eqPrefix(Name a, Name b) {
        if (a == b) return true;
        if (a == null || b == null) return false;
        return a.equals(b);
    }

    // --- Display ---

    @Override
    public String toString() {
        if (tag == ANONYMOUS) return "[anonymous]";
        StringBuilder sb = new StringBuilder();
        appendTo(sb);
        return sb.toString();
    }

    private void appendTo(StringBuilder sb) {
        if (tag == ANONYMOUS) return;
        if (prefix != null && prefix.tag != ANONYMOUS) {
            prefix.appendTo(sb);
            sb.append('.');
        }
        if (tag == STR) sb.append(str);
        else if (tag == NUM) sb.append(num);
    }

    /** Number of interned names (for diagnostics). */
    public static int internedCount() {
        return internTable.size();
    }
}
