import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import java.math.BigInteger;
import java.util.*;

/** Genuine v2 two-file program loaded from an application resource, without a toolchain. */
public final class GeneralInteropSmoke {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static void refuse(String code, Runnable action) {
        try { action.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException error) { check(code.equals(error.code())); }
    }
    public static void main(String[] args) throws Exception {
        String manifest = "be9bd183156ae082eb532a0bc8cb4eff19949813476e17985a6d48420c98f1aa";
        LeanFunction retained;
        try (Lean runtime = Lean.open();
             LeanProject p = runtime.loadArtifact(GeneralInteropSmoke.class.getClassLoader(), "lean/general-interop.zip", manifest)) {
            retained = p.function("Demo.sumArgs");
            check(retained.arity() == 3);
            check(retained.invoke(20L, 21L, true).equals(n(42)));
            check(p.call("Demo.negate", -42L).equals(n(42)));
            check(p.call("Demo.greet", "λ😀\0", true).equals("λ😀\0!"));
            check(p.call("Demo.constantBool").equals(true));
            check(p.call("Demo.unitIdentity", LeanUnit.INSTANCE) == LeanUnit.INSTANCE);
            check(p.call("Demo.pairIdentity", List.of(true, 42L)).equals(List.of(true, n(42))));
            check(p.call("Demo.pairSecond", List.of(false, 42L)).equals(n(42)));
            check(p.call("Demo.discardList", List.of(1L, 2L)).equals(n(19)));
            check(p.call("Demo.reverseList", List.of(1L, 2L, 3L)).equals(List.of(n(3), n(2), n(1))));
            check(p.call("Demo.emptyList").equals(List.of()));
            check(p.call("Demo.optionUnit", Optional.of(LeanUnit.INSTANCE)).equals(Optional.of(LeanUnit.INSTANCE)));
            check(p.call("Demo.optionUnit", Optional.empty()).equals(Optional.empty()));
            check(p.call("Demo.nestedOption", Optional.of(Optional.empty())).equals(Optional.of(Optional.empty())));
            check(p.call("Demo.pairs", 4L).equals(List.of(List.of(true, n(4)), List.of(false, n(5)))));
            IOResult<?> effect = (IOResult<?>) p.call("Demo.effect", true, List.of(20L, 22L));
            check(effect.value().equals(Optional.of(List.of("sum", n(42)))) && effect.stdout().equals("effect\n"));
            check(((IOResult<?>) p.call("Demo.main")).stdout().equals("main\n"));
            check(((IOResult<?>) p.call("Demo.other")).stdout().equals("other\n"));
            refuse("ArityMismatch", () -> retained.invoke(1L));
            refuse("UnsupportedArgumentType", () -> p.call("Demo.reverseList", true));
            refuse("InvalidArgument", () -> p.call("Demo.pairIdentity", List.of(true)));
            refuse("EntryNotAdmitted", () -> p.function("unselected"));
            refuse("EntryRejected", () -> p.runMain());
            check(retained.invoke(20L, 21L, true).equals(n(42)));
            ArrayList<Long> input = new ArrayList<>(List.of(1L, 2L));
            List<?> output = (List<?>) p.call("Demo.reverseList", input); input.set(0, 9L);
            check(output.equals(List.of(n(2), n(1))));
            try { output.clear(); throw new AssertionError("Mutable result"); }
            catch (UnsupportedOperationException expected) { checks++; }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            Object someUnit = Clojure.read("{:some nil}");
            check(Clojure.var("ansatz.lean.jvm", "call").invoke(p, "Demo.optionUnit", someUnit).equals(someUnit));
            Object nested = Clojure.read("{:some {:some 42}}");
            check(Boolean.TRUE.equals(Clojure.var("clojure.core", "=").invoke(
                Clojure.var("ansatz.lean.jvm", "call").invoke(p, "Demo.nestedOption", nested), nested)));
            check(Clojure.var("ansatz.lean.jvm", "call").invoke(p, "Demo.optionUnit", (Object) null) == null);
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        try { retained.invoke(1L, 2L, true); throw new AssertionError("Closed handle"); }
        catch (IllegalStateException expected) { checks++; }
        System.out.println("PASS GeneralInteropSmoke checks=" + checks + "; genuine v2 application JAR, no native toolchain");
    }
}
