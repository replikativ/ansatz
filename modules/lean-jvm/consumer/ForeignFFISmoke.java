import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.math.BigInteger;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

/** Actual foreign declarations and synchronous IO bindings in a prepared artifact.
 * Pure implementations must satisfy their Lean declaration's purity contract. */
public final class ForeignFFISmoke {
    private static final String MANIFEST = "860bed68ede444aca008e5e6fb570c86fe7a4248bda9cd7761d0b20f2dd9dfab";
    private static final String RESOURCE = "lean/foreign-ffi.zip";
    private static void check(boolean ok) { if (!ok) throw new AssertionError("Foreign FFI contract"); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static LeanProject load(Lean runtime, HostBindings bindings) throws Exception {
        return runtime.loadArtifact(ForeignFFISmoke.class.getClassLoader(), RESOURCE, MANIFEST, bindings);
    }
    private static HostBindings.Builder required(AtomicInteger effects, Function<List<Object>, Object> read) {
        return HostBindings.builder()
            .pure("HostInterop.length", "length/1", xs -> {
                String value = (String) xs.get(0); return n(value.codePointCount(0, value.length()));
            })
            .pureFactory("HostInterop.makeMessage", "message/1", signature -> {
                check(signature.argumentTypes().size() == 2);
                LeanType.Constructor ctor = signature.resultType().constructors().get(0);
                return xs -> ctor.create(List.of(xs.get(0), xs.get(1)));
            })
            .pure("HostInterop.zero", "zero/1", xs -> { check(xs.isEmpty()); return n(0); })
            .io("HostInterop.readConfig", "read/1", xs -> { effects.incrementAndGet(); check(xs.size() == 1); return read.apply(xs); });
    }
    private static Object io(LeanProject project, String entry, String key) {
        return ((IOResult<?>) project.call(entry, key)).value();
    }
    private static void rejected(String code, Runnable action) {
        try { action.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException failure) { check(failure.code().equals(code) && failure.getCause() == null); }
    }
    public static void main(String[] args) throws Exception {
        try (Lean runtime = Lean.open()) {
            AtomicInteger effects = new AtomicInteger(); LeanData detached;
            try (LeanProject project = load(runtime, required(effects, xs -> "host:" + xs.get(0)).build())) {
                check(project.call("HostInterop.useLength", "λ😀").equals(n(2)));
                detached = (LeanData) project.call("HostInterop.useMessage", n(42), true);
                check(detached.field(0).equals(n(42)) && detached.field(1).equals(true));
                check(project.call("HostInterop.useZero", n(9)).equals(n(0)));
                check(io(project, "HostInterop.describe", "key").equals("host:key"));
                check(effects.get() == 1);
                check(io(project, "HostInterop.runReference", "key").equals("reference:key"));
                check(effects.get() == 1);
            }
            check(detached.field(0).equals(n(42)));
            AtomicInteger factories = new AtomicInteger();
            try {
                load(runtime, HostBindings.builder().pureFactory("HostInterop.makeMessage", "partial/1", signature -> {
                    factories.incrementAndGet(); return xs -> null;
                }).build());
                throw new AssertionError("Missing required foreign bindings accepted");
            } catch (LeanException failure) { check(failure.code().equals("BindingRejected") && factories.get() == 0); }
            try {
                load(runtime, required(new AtomicInteger(), xs -> "unused").pure("HostInterop.referenceRead", "wrong-effect/1", xs -> "unused").build());
                throw new AssertionError("Mismatched IO effect accepted");
            } catch (LeanException failure) { check(failure.code().equals("BindingRejected")); }
            AtomicInteger overridden = new AtomicInteger();
            try (LeanProject project = load(runtime, required(new AtomicInteger(), xs -> "unused")
                    .ioFactory("HostInterop.referenceRead", "override/1", signature -> {
                        check(signature.argumentTypes().size() == 1);
                        return xs -> { overridden.incrementAndGet(); return "override:" + xs.get(0); };
                    }).build())) {
                check(io(project, "HostInterop.runReference", "key").equals("override:key"));
                check(overridden.get() == 1);
            }
            for (boolean eof : new boolean[]{false, true}) {
                AtomicInteger count = new AtomicInteger();
                try (LeanProject project = load(runtime, required(count, xs -> {
                    if (xs.get(0).equals("key")) throw eof ? LeanIOError.unexpectedEof() : LeanIOError.userError("explicit failure");
                    return "recovered";
                }).build())) {
                    String value = (String) io(project, "HostInterop.describe", "key");
                    check(value.startsWith("caught:") && (eof || value.contains("explicit failure")));
                    check(count.get() == 1);
                    check(io(project, "HostInterop.describe", "next").equals("recovered"));
                    check(count.get() == 2);
                }
            }
            AtomicInteger failed = new AtomicInteger();
            try (LeanProject project = load(runtime, required(failed, xs -> { throw new IllegalStateException("host failure"); }).build())) {
                rejected("HostFailure", () -> io(project, "HostInterop.describe", "key"));
                rejected("RuntimeBoundary", () -> io(project, "HostInterop.describe", "key"));
                check(failed.get() == 1);
            }
            AssertionError fatal = new AssertionError("fatal host error"); AtomicInteger fatals = new AtomicInteger();
            try (LeanProject project = load(runtime, required(fatals, xs -> { throw fatal; }).build())) {
                try { io(project, "HostInterop.describe", "key"); throw new AssertionError("Fatal error swallowed"); }
                catch (AssertionError failure) { check(failure == fatal); }
                check(fatals.get() == 1);
            }
            AtomicInteger canceled = new AtomicInteger();
            try (LeanProject project = load(runtime, required(canceled, xs -> { Thread.currentThread().interrupt(); return "ignored"; }).build())) {
                try { rejected("Cancelled", () -> io(project, "HostInterop.describe", "key")); check(Thread.currentThread().isInterrupted()); }
                finally { Thread.interrupted(); }
                check(canceled.get() == 1);
            }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IFn clojureCheck = (IFn) Clojure.var("clojure.core", "eval").invoke(Clojure.read(
                "(fn [runtime input sha] (with-open [p (ansatz.lean.jvm/load-artifact runtime input sha " +
                "{\"HostInterop.length\" {:implementation-id \"clj-length/1\" :fn count} " +
                "\"HostInterop.makeMessage\" {:implementation-id \"clj-message/1\" :factory (fn [{:keys [result-type]}] " +
                "(let [ctor (first (.constructors result-type))] (fn [n enabled] (.create ctor [n enabled]))))} " +
                "\"HostInterop.zero\" {:implementation-id \"clj-zero/1\" :fn (fn [] 0)} " +
                "\"HostInterop.readConfig\" {:effect :io :implementation-id \"clj-read/1\" :fn (fn [key] (str \"clj:\" key))}})] " +
                "(= \"clj:key\" (:value (ansatz.lean.jvm/call p \"HostInterop.describe\" \"key\"))))))"));
            try (var input = ForeignFFISmoke.class.getClassLoader().getResourceAsStream(RESOURCE)) {
                check(Boolean.TRUE.equals(clojureCheck.invoke(runtime, input, MANIFEST)));
            }
        }
        System.out.println("PASS foreign pure/IO bindings, native fallback, detached values, explicit IO errors, failures and cancellation");
    }
}
