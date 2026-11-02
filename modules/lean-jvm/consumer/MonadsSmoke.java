import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/** Native-prepared closed monad runners through the packaged JVM-only facade. */
public final class MonadsSmoke {
    private static final String MANIFEST = "fdb74ddb2d96a3a0bf07f188f20a0396e01ed888429457d173af174ec5088aa7";
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static LeanProject open(Lean runtime) throws java.io.IOException {
        return runtime.loadArtifact(MonadsSmoke.class.getClassLoader(), "lean/monad-conformance.zip", MANIFEST);
    }
    private static Object io(Object result) {
        IOResult<?> effect = (IOResult<?>) result;
        check(effect.stdout().isEmpty() && effect.stderr().isEmpty());
        return effect.value();
    }
    private static void branch(Object result, boolean error, Object expected) {
        LeanChoice choice = (LeanChoice) result;
        check(choice.isLeft() == error);
        check(choice.value().equals(expected));
    }
    private static void userError(Lean runtime, String entry, String input, String message, boolean truncated) throws java.io.IOException {
        try (LeanProject failed = open(runtime)) {
            try {
                if (input == null) failed.call(entry); else failed.call(entry, input);
                throw new AssertionError("Expected GuestIOError");
            } catch (LeanException error) {
                check(error.code().equals("GuestIOError"));
                check(error.getCause() == null && error.getSuppressed().length == 0);
                Map<String, Object> expected = truncated
                    ? Map.of("kind", "userError", "message", message, "messageTruncated", true)
                    : Map.of("kind", "userError", "message", message);
                check(error.details().equals(expected));
                check(error.details().values().stream().allMatch(value -> value instanceof String || value instanceof Boolean));
                try { error.details().put("owner", new Object()); throw new AssertionError("Mutable details"); }
                catch (UnsupportedOperationException expectedFailure) { checks++; }
            }
            try { failed.call("retainedRead"); throw new AssertionError("Failed project reusable"); }
            catch (LeanException expected) { check(expected.code().equals("RuntimeBoundary")); }
        }
        checks++; // terminal branch must still close successfully
    }
    public static void main(String[] args) throws Exception {
        LeanFunction retained;
        try (Lean runtime = Lean.open(); LeanProject project = open(runtime)) {
            retained = project.function("retainedRead");
            for (boolean fail : new boolean[]{false, true}) {
                List<?> state = (List<?>) project.call("readerStateExcept", 3L, 10L, fail);
                branch(state.get(0), fail, fail ? "body" : n(13));
                check(state.get(1).equals(n(13)));
            }
            branch(project.call("stateRollback", 10L), false, List.of(n(11), n(11)));
            check(project.call("stRefs", 10L).equals(List.of(n(10), List.of(n(15), true))));
            for (String entry : new String[]{"estFinally", "exceptTFinally"}) {
                for (boolean bodyFails : new boolean[]{false, true}) {
                    for (boolean cleanupFails : new boolean[]{false, true}) {
                        boolean error = bodyFails || cleanupFails;
                        Object expected = cleanupFails ? "cleanup" : bodyFails ? "body" : List.of(n(7), Optional.of(n(7)));
                        branch(project.call(entry, bodyFails, cleanupFails), error, expected);
                    }
                }
            }
            check(io(project.call("baseIORunner", 10L)).equals(List.of(n(10), n(15))));
            branch(io(project.call("eioRunner", false)), false, n(23));
            branch(io(project.call("eioRunner", true)), true, "typed");
            branch(io(project.call("stateRefRunner", 3L, 10L)), false, List.of(n(123), n(123)));
            check(io(project.call("stateRefDiscard", 10L)).equals(n(15)));
            check(io(project.call("ioCatchFinally", 10L)).equals(List.of(n(21), n(121), n(1121))));
            LeanFunction bump = project.function("retainedBump");
            LeanFunction st = project.function("stRefs");
            LeanFunction base = project.function("baseIORunner");
            check(io(retained.invoke()).equals(n(40)));
            check(io(bump.invoke(2L)).equals(n(42)));
            check(io(bump.invoke(3L)).equals(n(45)));
            check(io(retained.invoke()).equals(n(45)));
            for (int i = 0; i < 3; i++) {
                check(st.invoke(10L).equals(List.of(n(10), List.of(n(15), true))));
                check(io(base.invoke(10L)).equals(List.of(n(10), n(15))));
                check(io(retained.invoke()).equals(n(45)));
            }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IFn function = (IFn) Clojure.var("ansatz.lean.jvm", "function").invoke(project, "stateRollback");
            check(Boolean.TRUE.equals(Clojure.var("clojure.core", "=").invoke(
                function.invoke(10L), Clojure.read("{:ok [11 11]}"))));

            userError(runtime, "uncaughtUserError", "λ😀\u0000guest", "λ😀\u0000guest", false);
            check(io(retained.invoke()).equals(n(45)));
            userError(runtime, "uncaughtUserError", "", "", false);
            check(io(retained.invoke()).equals(n(45)));
            String maximum = "x".repeat(2048);
            userError(runtime, "uncaughtUserError", maximum, maximum, false);
            check(io(retained.invoke()).equals(n(45)));
            String prefix = "x".repeat(2047);
            userError(runtime, "uncaughtUserError", prefix + "😀tail", prefix, true);
            check(io(retained.invoke()).equals(n(45)));
            // AUTO preparation records this IO Unit entry with the v2 codec.
            userError(runtime, "legacyUserError", null, "legacy guest error", false);
            check(io(retained.invoke()).equals(n(45)));
            try (LeanProject failed = open(runtime)) {
                try { failed.call("otherIOError"); throw new AssertionError("Expected other IO error"); }
                catch (LeanException error) {
                    check(error.code().equals("GuestIOError") && error.details().isEmpty());
                    check(error.getCause() == null && error.getSuppressed().length == 0);
                }
                try { failed.call("retainedRead"); throw new AssertionError("Failed project reusable"); }
                catch (LeanException expected) { check(expected.code().equals("RuntimeBoundary")); }
            }
            checks++;
            check(io(retained.invoke()).equals(n(45)));
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        try { retained.invoke(); throw new AssertionError("Closed handle"); }
        catch (IllegalStateException expected) { checks++; }
        System.out.println("PASS MonadsSmoke checks=" + checks + "; public Java/Clojure monad runners and bounded IO errors, JVM-only artifact");
    }
}
