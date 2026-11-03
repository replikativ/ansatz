import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.math.BigInteger;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/** Real native-prepared multi-module code, both reference and host execution. */
public final class PureFFISmoke {
    private static final String MANIFEST = "da1169a358c744b5c07eb4c68dd3a45b5e70638f8141b98f2f153e293ac457ac";
    private static void check(boolean ok) { if (!ok) throw new AssertionError("Pure FFI contract"); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static LeanProject load(Lean runtime, HostBindings bindings) throws Exception {
        return runtime.loadArtifact(PureFFISmoke.class.getClassLoader(), "lean/pure-ffi.zip", MANIFEST, bindings);
    }
    private static HostBindings bindings(AtomicInteger calls) {
        return HostBindings.builder()
            .pure("Interop.normalize", "normalize/1", xs -> { calls.getAndUpdate(mask -> mask | 1); return ((BigInteger) xs.get(0)).add(n(1)); })
            .pure("Interop.normalizeMessage", "message/1", xs -> {
                calls.getAndUpdate(mask -> mask | 2); LeanData message = (LeanData) xs.get(0);
                return message.constructor().create(List.of(((BigInteger) message.field(0)).add(n(1)), message.field(1)));
            })
            .pureFactory("Interop.combine", "combine/1", signature -> {
                check(signature.argumentTypes().size() == 3);
                LeanType.Constructor constructor = signature.resultType().constructors().get(0);
                return xs -> {
                    calls.getAndUpdate(mask -> mask | 4); String label = (String) xs.get(2);
                    return constructor.create(List.of(((BigInteger) xs.get(0)).add(n(label.codePointCount(0, label.length()))), xs.get(1)));
                };
            })
            .pure("Interop.constant", "constant/1", xs -> { calls.getAndUpdate(mask -> mask | 8); check(xs.isEmpty()); return n(7); })
            .pure("Interop.twice", "twice/1", xs -> { calls.getAndUpdate(mask -> mask | 16); return ((BigInteger) xs.get(0)).multiply(n(2)); })
            .pure("Interop.echo", "echo/1", xs -> { calls.getAndUpdate(mask -> mask | 32); return xs.get(0); })
            .pure("Interop.isA", "is-a/1", xs -> { calls.getAndUpdate(mask -> mask | 64); return ((Number) xs.get(0)).intValue() == 'a'; })
            .build();
    }
    private static LeanData exercise(LeanProject project) {
        check(project.call("Interop.initialValue", n(1)).equals(n(7)));
        check(project.call("Interop.pipeline", n(41)).equals(n(46)));
        LeanData message = (LeanData) project.call("Interop.process", n(42));
        check(message.field(0).equals(n(43)) && message.field(1).equals(true));
        LeanData combined = (LeanData) project.call("Interop.callCombine", n(7));
        check(combined.field(0).equals(n(10)) && combined.field(1).equals(true));
        LeanData unicode = (LeanData) project.call("Interop.combine", n(7), true, "λ😀");
        check(unicode.field(0).equals(n(9)));
        check(project.call("Interop.callConstant", n(5)).equals(n(12)));
        check(project.call("Interop.mapped", n(4)).equals(n(18)));
        check(project.call("Interop.echo", List.of(n(1), n(2), n(3))).equals(List.of(n(1), n(2), n(3))));
        check(project.call("Interop.containsA", "λ😀a").equals(true));
        check(project.call("Interop.containsA", "λ😀").equals(false));
        return message;
    }
    private static void rejected(String code, Runnable action) {
        try { action.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException failure) { check(code.equals(failure.code())); check(failure.getCause() == null); }
    }
    public static void main(String[] args) throws Exception {
        AtomicInteger calls = new AtomicInteger(); LeanData detached;
        try (Lean runtime = Lean.open()) {
            try (LeanProject reference = load(runtime, HostBindings.empty())) { exercise(reference); }
            try (LeanProject host = load(runtime, bindings(calls))) {
                check((calls.get() & 1) != 0); // initializer used the selected implementation
                detached = exercise(host);
            }
            check(calls.get() == 127 && detached.field(0).equals(n(43)));
            AtomicInteger factories = new AtomicInteger();
            try {
                load(runtime, HostBindings.builder()
                    .pureFactory("Interop.combine", "factory/1", signature -> { factories.incrementAndGet(); return xs -> xs.get(0); })
                    .pure("Missing.binding", "missing/1", xs -> xs.get(0)).build());
                throw new AssertionError("Invalid selection accepted");
            } catch (LeanException failure) { check(failure.code().equals("BindingRejected") && factories.get() == 0); }
            for (String name : List.of("Interop.pipeline", "Missing.binding")) {
                try {
                    load(runtime, HostBindings.builder().pure(name, "invalid/1", xs -> xs.get(0)).build());
                    throw new AssertionError("Unadmitted binding accepted");
                } catch (LeanException failure) { check(failure.code().equals("BindingRejected")); }
            }
            try {
                runtime.loadArtifact(PureFFISmoke.class.getClassLoader(), "lean/datatypes.zip",
                    "06f1ccafd17b4cdc8915b2e41d49e8e9741b8765fa2b281b60bcce636c5daf25",
                    HostBindings.builder().pure("DatatypeExample.eval", "old-cohort/1", xs -> n(0)).build());
                throw new AssertionError("Old evidence gained binding authority");
            } catch (LeanException failure) { check(failure.code().equals("BindingRejected")); }
            try {
                load(runtime, HostBindings.builder().pure("Interop.normalize", "failed-initializer/1", xs -> { throw new IllegalArgumentException("init failed"); }).build());
                throw new AssertionError("Failed initializer accepted");
            } catch (LeanException failure) { check(failure.code().equals("HostFailure")); }
            try (LeanProject bad = load(runtime, HostBindings.builder().pure("Interop.normalizeMessage", "bad/1", xs -> "not a Message").build())) {
                rejected("HostFailure", () -> bad.call("Interop.process", n(41)));
                rejected("RuntimeBoundary", () -> bad.call("Interop.process", n(41)));
            }
            AssertionError original = new AssertionError("host error");
            try (LeanProject bad = load(runtime, HostBindings.builder().pure("Interop.normalizeMessage", "error/1", xs -> { throw original; }).build())) {
                try { bad.call("Interop.process", n(41)); throw new AssertionError("Fatal error swallowed"); }
                catch (AssertionError failure) { check(failure == original); }
            }
            try (LeanProject canceled = load(runtime, HostBindings.builder().pure("Interop.normalizeMessage", "cancel/1", xs -> {
                Thread.currentThread().interrupt(); return xs.get(0);
            }).build())) {
                try { rejected("Cancelled", () -> canceled.call("Interop.process", n(41))); check(Thread.currentThread().isInterrupted()); }
                finally { Thread.interrupted(); }
            }
            try (LeanProject badPredicate = load(runtime, HostBindings.builder().pure("Interop.isA", "failed-predicate/1", xs -> {
                throw new IllegalArgumentException("predicate failed");
            }).build())) {
                rejected("HostFailure", () -> badPredicate.call("Interop.containsA", "abc"));
            }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IFn clojureCheck = (IFn) Clojure.var("clojure.core", "eval").invoke(Clojure.read(
                "(fn [runtime input sha] (with-open [p (ansatz.lean.jvm/load-artifact runtime input sha " +
                "{\"Interop.normalize\" {:implementation-id \"clj/1\" :fn inc} " +
                "\"Interop.normalizeMessage\" {:implementation-id \"record/1\" :fn (fn [message] (update-in message [:lean/fields 0] inc))}})] " +
                "(and (= 46 (ansatz.lean.jvm/call p \"Interop.pipeline\" 41)) " +
                "(= [43 true] (:lean/fields (ansatz.lean.jvm/call p \"Interop.process\" 42))))))"));
            try (var input = PureFFISmoke.class.getClassLoader().getResourceAsStream("lean/pure-ffi.zip")) {
                check(Boolean.TRUE.equals(clojureCheck.invoke(runtime, input, MANIFEST)));
            }
        }
        System.out.println("PASS pure JVM/Clojure bindings, native reference values, datatypes, nullary/arity3, optimized callers and failure retirement");
    }
}
