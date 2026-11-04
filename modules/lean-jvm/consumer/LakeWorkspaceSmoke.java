import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.math.BigInteger;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/** Prepared cross-package code: no source directories, Lake or native toolchain. */
public final class LakeWorkspaceSmoke {
    private static final String MANIFEST = "c8b61e334e62e510880bc345f4f9f5754f7c6d364fbcd914ae9eee1ec11c99da";
    private static void check(boolean value) { if (!value) throw new AssertionError("Lake workspace contract"); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static LeanProject load(Lean runtime, HostBindings bindings) throws java.io.IOException {
        return runtime.loadArtifact(LakeWorkspaceSmoke.class.getClassLoader(), "lean/lake-workspace.zip", MANIFEST, bindings);
    }
    public static void main(String[] args) throws Exception {
        LeanData detached;
        try (Lean runtime = Lean.open()) {
            try (LeanProject project = load(runtime, HostBindings.empty())) {
                check(project.call("App.calculate", n(32)).equals(n(42)));
                detached = (LeanData) project.call("App.account", n(35));
                check(detached.field(0).equals(n(42)) && detached.field(1).equals(true));
                check(project.call("Domain.credit", detached, n(1)) instanceof LeanData);
            }
            AtomicInteger callbacks = new AtomicInteger();
            HostBindings bindings = HostBindings.builder().pureFactory("Domain.credit", "credit/1", signature -> {
                LeanType.Constructor ctor = signature.resultType().constructors().get(0);
                return values -> {
                    callbacks.incrementAndGet(); LeanData account = (LeanData) values.get(0);
                    return ctor.create(List.of(((BigInteger) account.field(0)).add((BigInteger) values.get(1)), account.field(1)));
                };
            }).build();
            try (LeanProject project = load(runtime, bindings)) {
                check(project.call("App.calculate", n(32)).equals(n(42)));
                LeanData result = (LeanData) project.call("Domain.credit", detached, n(1));
                check(result.field(0).equals(n(43)) && callbacks.get() == 2);
            }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IFn clojureCheck = (IFn) Clojure.var("clojure.core", "eval").invoke(Clojure.read(
                "(fn [runtime input sha] (with-open [p (ansatz.lean.jvm/load-artifact runtime input sha)] " +
                "(and (= 42 (ansatz.lean.jvm/call p \"App.calculate\" 32)) " +
                "(= [43 true] (:lean/fields (ansatz.lean.jvm/call p \"Domain.credit\" " +
                "(ansatz.lean.jvm/call p \"App.account\" 35) 1))))))"));
            try (var input = LakeWorkspaceSmoke.class.getClassLoader().getResourceAsStream("lean/lake-workspace.zip")) {
                check(Boolean.TRUE.equals(clojureCheck.invoke(runtime, input, MANIFEST)));
            }
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.workspace")) == null);
        }
        check(detached.field(0).equals(n(42)));
        System.out.println("PASS JVM-only Lake workspace, dependency initialization, nominal values and Java/Clojure host calls");
    }
}
