// Ansatz kernel — Declaration storage.

package ansatz.kernel;

/**
 * Stores a kernel declaration (constant info).
 * Single class with union-of-fields to avoid virtual dispatch.
 *
 * <p>Variants: AXIOM, DEF, THM, OPAQUE, QUOT, INDUCT, CTOR, RECURSOR
 */
public final class ConstantInfo {

    public static final byte AXIOM = 0;
    public static final byte DEF = 1;
    public static final byte THM = 2;
    public static final byte OPAQUE = 3;
    public static final byte QUOT = 4;
    public static final byte INDUCT = 5;
    public static final byte CTOR = 6;
    public static final byte RECURSOR = 7;

    // Hint constants
    public static final int HINTS_OPAQUE = -1;
    public static final int HINTS_ABBREV = 0;
    // hints > 0: regular(height)

    public final byte tag;
    public final Name name;
    public final Object[] levelParams;  // Name[]
    public final Expr type;

    // DEF/THM/OPAQUE
    public Expr value;          // mutable: cleared for THM/OPAQUE after check
    public int hints;           // DEF only: -1=opaque, 0=abbrev, >0=regular(height)
    public byte safety;         // 0=safe, 1=unsafe, 2=partial

    // QUOT
    public Object quotKind;     // keyword

    // INDUCT
    public int numParams;
    public int numIndices;
    public Name[] ctors;        // constructor names
    public Object[] all;        // all declaration names in mutual group
    public int numNested;
    public boolean isRec;
    public boolean isReflexive;
    public boolean isUnsafe;

    // CTOR
    public Name inductName;
    public int cidx;
    public int numFields;

    // RECURSOR
    public int numMotives;
    public int numMinors;
    public RecursorRule[] rules;
    public boolean isK;

    private ConstantInfo(byte tag, Name name, Object[] levelParams, Expr type) {
        this.tag = tag;
        this.name = name;
        this.levelParams = levelParams;
        this.type = type;
    }

    // --- Recursor rule ---

    public static final class RecursorRule {
        public final Name ctor;
        public final int nfields;
        public final Expr rhs;

        public RecursorRule(Name ctor, int nfields, Expr rhs) {
            this.ctor = ctor;
            this.nfields = nfields;
            this.rhs = rhs;
        }
    }

    // --- Static factories ---

    public static ConstantInfo mkAxiom(Name name, Object[] levelParams, Expr type, boolean unsafe) {
        ConstantInfo ci = new ConstantInfo(AXIOM, name, levelParams, type);
        ci.isUnsafe = unsafe;
        return ci;
    }

    public static ConstantInfo mkDef(Name name, Object[] levelParams, Expr type, Expr value,
                                     int hints, byte safety, Object[] all) {
        ConstantInfo ci = new ConstantInfo(DEF, name, levelParams, type);
        ci.value = value;
        ci.hints = hints;
        ci.safety = safety;
        ci.all = all;
        return ci;
    }

    public static ConstantInfo mkThm(Name name, Object[] levelParams, Expr type, Expr value, Object[] all) {
        ConstantInfo ci = new ConstantInfo(THM, name, levelParams, type);
        ci.value = value;
        ci.all = all;
        return ci;
    }

    public static ConstantInfo mkOpaque(Name name, Object[] levelParams, Expr type, Expr value,
                                        Object[] all, boolean unsafe) {
        ConstantInfo ci = new ConstantInfo(OPAQUE, name, levelParams, type);
        ci.value = value;
        ci.all = all;
        ci.isUnsafe = unsafe;
        return ci;
    }

    public static ConstantInfo mkQuot(Name name, Object[] levelParams, Expr type, Object kind) {
        ConstantInfo ci = new ConstantInfo(QUOT, name, levelParams, type);
        ci.quotKind = kind;
        return ci;
    }

    public static ConstantInfo mkInduct(Name name, Object[] levelParams, Expr type,
                                        int numParams, int numIndices, Object[] all, Name[] ctors,
                                        int numNested, boolean isRec, boolean isReflexive, boolean isUnsafe) {
        ConstantInfo ci = new ConstantInfo(INDUCT, name, levelParams, type);
        ci.numParams = numParams;
        ci.numIndices = numIndices;
        ci.all = all;
        ci.ctors = ctors;
        ci.numNested = numNested;
        ci.isRec = isRec;
        ci.isReflexive = isReflexive;
        ci.isUnsafe = isUnsafe;
        return ci;
    }

    public static ConstantInfo mkCtor(Name name, Object[] levelParams, Expr type,
                                      Name inductName, int cidx, int numParams, int numFields, boolean isUnsafe) {
        ConstantInfo ci = new ConstantInfo(CTOR, name, levelParams, type);
        ci.inductName = inductName;
        ci.cidx = cidx;
        ci.numParams = numParams;
        ci.numFields = numFields;
        ci.isUnsafe = isUnsafe;
        return ci;
    }

    public static ConstantInfo mkRecursor(Name name, Object[] levelParams, Expr type,
                                          Object[] all, int numParams, int numIndices,
                                          int numMotives, int numMinors,
                                          RecursorRule[] rules, boolean isK, boolean isUnsafe) {
        ConstantInfo ci = new ConstantInfo(RECURSOR, name, levelParams, type);
        ci.all = all;
        ci.numParams = numParams;
        ci.numIndices = numIndices;
        ci.numMotives = numMotives;
        ci.numMinors = numMinors;
        ci.rules = rules;
        ci.isK = isK;
        ci.isUnsafe = isUnsafe;
        return ci;
    }

    // --- Predicates ---

    public boolean isDef() { return tag == DEF; }
    public boolean isThm() { return tag == THM; }
    public boolean isAxiom() { return tag == AXIOM; }
    public boolean isInduct() { return tag == INDUCT; }
    public boolean isCtor() { return tag == CTOR; }
    public boolean isRecursor() { return tag == RECURSOR; }
    public boolean isQuot() { return tag == QUOT; }
    public boolean isOpaq() { return tag == OPAQUE; }

    /**
     * Get the value for delta reduction: definitions AND theorems, never opaques.
     * This is the kernel's `constant_info::has_value()` (declaration.h, v4.33.1:466 —
     * `is_theorem() || is_definition()`), the predicate `type_checker::is_delta` consults.
     * lean4#12973 ("theorems are opaque") did not change that predicate: the kernel still
     * unfolds a theorem when reduction reaches it, and Mathlib relies on it — a `rfl` such as
     * `Rat.instEncodable._proof_3` only closes because `And.rec` sees through the abstracted
     * auxiliary theorem `_proof_1` to its `And.intro`. Hiding theorem bodies (PR #87, 2026-09)
     * made that declaration fail against the reference. A store may still load theorems
     * WITHOUT bodies for proving sessions (`:defs-only`); then `value` is null and the
     * unfolding simply does not happen — a completeness, never a soundness, difference.
     * Returns null for axioms, inductives, constructors, recursors, opaques.
     */
    public Expr getValue() {
        return (tag == DEF || tag == THM) ? value : null;
    }

    /**
     * Get reducibility hints. Returns HINTS_OPAQUE for non-definitions.
     */
    public int getHints() {
        return tag == DEF ? hints : HINTS_OPAQUE;
    }

    @Override
    public String toString() {
        return name.toString();
    }
}
