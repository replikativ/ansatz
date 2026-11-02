import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import java.math.BigInteger;
import java.util.*;

/** Unchanged upstream proof-backed sort in a JVM-only application JAR. */
public final class SortSmoke {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    public static void main(String[] args) throws Exception {
        String manifest = "48bf70cd8028cd06cf2051e3e80ff2e57352d56f959c3a0a0b0e845183ade4ba";
        LeanFunction retained;
        try (Lean runtime = Lean.open();
             LeanProject p = runtime.loadArtifact(SortSmoke.class.getClassLoader(), "lean/fp-lean-sort.zip", manifest)) {
            retained = p.function("Tutorial.sortNats");
            for (int size = 0; size < 25; size++) {
                List<Long> input = new ArrayList<>();
                List<BigInteger> sorted = new ArrayList<>();
                for (long i = 0; i < size; i++) { input.add(size - i - 1); sorted.add(BigInteger.valueOf(i)); }
                IOResult<?> result = (IOResult<?>) p.call("Tutorial.sortAndOriginal", input);
                List<BigInteger> original = input.stream().map(BigInteger::valueOf).toList();
                check(result.value().equals(List.of(sorted, original)));
                check(result.stdout().isEmpty());
                if (!input.isEmpty()) input.set(0, 999L);
                check(result.value().equals(List.of(sorted, original)));
                check(((IOResult<?>) retained.invoke(sorted)).value().equals(sorted));
            }
            IOResult<?> strings = (IOResult<?>) p.call("Tutorial.sortStrings", List.of("😀", "\ue000", "β", "a"));
            check(strings.value().equals(List.of("a", "β", "\ue000", "😀")));
            IOResult<?> trace = (IOResult<?>) p.call("Tutorial.sortAndOriginal", List.of(3L, 2L, 1L));
            check(trace.stderr().equals("shared RC array to swap\n"));
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            Object result = Clojure.var("ansatz.lean.jvm", "call").invoke(p, "Tutorial.sortAndOriginal", Clojure.read("[3 2 1]"));
            check(Boolean.TRUE.equals(Clojure.var("clojure.core", "=").invoke(result,
                Clojure.read("{:value [[1 2 3] [3 2 1]] :stdout \"\" :stderr \"shared RC array to swap\\n\"}"))));
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        try { retained.invoke(List.of(1L)); throw new AssertionError("Closed handle"); }
        catch (IllegalStateException expected) { check(expected.getMessage().contains("closed")); }
        System.out.println("SORT_SMOKE checks=" + checks);
    }
}
