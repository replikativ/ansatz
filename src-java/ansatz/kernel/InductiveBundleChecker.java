package ansatz.kernel;

/**
 * Bundle-level inductive checker.
 *
 * <p>This is the kernel entrypoint for Lean-like inductive admission:
 * nested elimination -> ordinary inductive checking on the aux bundle ->
 * restoration -> comparison -> admission of the restored/original bundle.
 * Individual inductive, constructor, and recursor constants are rejected by
 * TypeChecker.checkConstant and must pass through this bundle path.
 */
public final class InductiveBundleChecker {
    private InductiveBundleChecker() {}

    public static Env checkBundle(Env env, InductiveBundle bundle, long fuel) {
        if (bundle == null || bundle.isEmpty()) {
            throw new RuntimeException("invalid inductive bundle: empty");
        }

        NestedElimResult elim = NestedInductiveEliminator.eliminate(env, bundle);
        InductiveBundle toCheck = elim.auxBundle;
        Env current;

        if (bundle.hasNestedInductives()) {
            boolean haveImportedRecursors = bundle.recursors != null && bundle.recursors.length > 0;
            if (haveImportedRecursors) {
                // Import path: lower the imported recursors to the aux form, check the aux
                // mutual bundle against them, and validate they restore to the nested form.
                ConstantInfo[] auxRecursors = InductiveChecker.lowerImportedRecursors(bundle, elim);
                InductiveBundle auxBundleWithRecursors = new InductiveBundle(
                    toCheck.levelParams,
                    toCheck.numParams,
                    toCheck.isUnsafe,
                    toCheck.inductives,
                    toCheck.ctors,
                    auxRecursors);
                try {
                    current = new InductiveChecker(env, auxBundleWithRecursors, fuel).run();
                } catch (RuntimeException ex) {
                    throw new RuntimeException("nested auxiliary inductive bundle check failed: " + ex.getMessage(), ex);
                }
                InductiveChecker.compareRestoredImportedBundle(bundle, elim, auxRecursors);
                return InductiveChecker.admitOriginalBundle(env, bundle);
            }

            // Generation path (surface-defined nested inductives, no imported recursors):
            // run the standard mutual recursor generator on the aux block — the nested
            // induction hypothesis (`motive_j kids`) comes out for free from the mutual
            // recursion — then restore each generated recursor to nested form and admit,
            // exactly as Lean's kernel add_inductive does (inductive.cpp:1116-1181).
            ConstantInfo[] auxRecursors;
            try {
                auxRecursors = new InductiveChecker(env, toCheck, fuel).generateAndCheckRecursors();
            } catch (RuntimeException ex) {
                throw new RuntimeException("nested auxiliary inductive bundle check failed: " + ex.getMessage(), ex);
            }
            ConstantInfo[] restoredRecursors = InductiveChecker.restoreGeneratedRecursors(bundle, elim, auxRecursors);
            InductiveBundle restoredBundle = new InductiveBundle(
                bundle.levelParams,
                bundle.numParams,
                bundle.isUnsafe,
                bundle.inductives,
                bundle.ctors,
                restoredRecursors);
            return InductiveChecker.admitOriginalBundle(env, restoredBundle);
        }

        try {
            current = new InductiveChecker(env, toCheck, fuel).run();
        } catch (RuntimeException ex) {
            throw new RuntimeException("inductive bundle check failed: " + ex.getMessage(), ex);
        }
        return current;
    }
}
