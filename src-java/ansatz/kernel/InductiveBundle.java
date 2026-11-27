package ansatz.kernel;

/**
 * The exported records of one mutual inductive block, as an export (Lean's NDJSON, a store)
 * delivers them: the inductive types, their constructors and their recursors, auxiliary nested
 * recursors included. The kernel never trusts these records: {@link InductiveImport} builds the
 * {@link InductiveDecl} they describe, generates the block, and compares every record with the
 * generated one.
 */
public final class InductiveBundle {
    public final Object[] levelParams;
    public final int numParams;
    public final boolean isUnsafe;

    public final ConstantInfo[] inductives;
    public final ConstantInfo[] ctors;
    public final ConstantInfo[] recursors;

    public InductiveBundle(Object[] levelParams, int numParams, boolean isUnsafe,
            ConstantInfo[] inductives, ConstantInfo[] ctors, ConstantInfo[] recursors) {
        this.levelParams = levelParams != null ? levelParams.clone() : new Object[0];
        this.numParams = numParams;
        this.isUnsafe = isUnsafe;
        this.inductives = inductives != null ? inductives.clone() : new ConstantInfo[0];
        this.ctors = ctors != null ? ctors.clone() : new ConstantInfo[0];
        this.recursors = recursors != null ? recursors.clone() : new ConstantInfo[0];
    }
}
