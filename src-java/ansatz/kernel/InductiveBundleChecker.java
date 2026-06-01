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

        try {
            current = new InductiveChecker(env, toCheck, fuel).run();
        } catch (RuntimeException ex) {
            throw new RuntimeException("inductive bundle check failed: " + ex.getMessage(), ex);
        }
        return current;
    }
}
