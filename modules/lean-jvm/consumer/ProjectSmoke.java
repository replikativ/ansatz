import ansatz.lean.jvm.Lean;
import ansatz.lean.jvm.LeanException;
import ansatz.lean.jvm.LeanProject;
import ansatz.lean.jvm.MainResult;
import clojure.java.api.Clojure;
import java.math.BigInteger;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.UnaryOperator;

/** Application-JAR consumer: no compiler, CLI, source checkout or runtime javac. */
public final class ProjectSmoke {
    private static void require(boolean ok, String message) {
        if (!ok) throw new AssertionError(message);
    }
    private static final class HostileNat extends BigInteger {
        HostileNat() { super("1"); }
        @Override public int signum() { throw new AssertionError("Subclass callback must not run"); }
    }
    public static void main(String[] args) throws Exception {
        final String manifest = "fc19283c5ada0f62f291ef11789b04d67874b57c293372a298d101aec0f8ae8b";
        UnaryOperator<BigInteger> retained;
        try (Lean lean = Lean.open()) {
            LeanProject project = lean.loadArtifact(ProjectSmoke.class.getClassLoader(), "lean/interop.zip", manifest);
            UnaryOperator<BigInteger> answer = project.natFunction("answer");
            UnaryOperator<String> echo = project.stringFunction("echo");
            retained = answer;
            for (BigInteger n : new BigInteger[]{BigInteger.ZERO, BigInteger.valueOf(42),
                    BigInteger.valueOf(Long.MAX_VALUE), BigInteger.ONE.shiftLeft(64), BigInteger.ONE.shiftLeft(200)}) {
                require(answer.apply(n).equals(n.shiftLeft(1).add(BigInteger.ONE)), "Exact Nat result");
            }
            String unicode = "\0λ😀e\u0301";
            require(echo.apply(unicode).equals("Hello, " + unicode), "Exact Unicode/NUL result");
            try { project.stringFunction("answer"); throw new AssertionError("Wrong signature accepted"); }
            catch (LeanException rejected) { require(rejected.code().equals("EntryRejected"), "Checked type rejection"); }
            try { answer.apply(BigInteger.valueOf(-1)); throw new AssertionError("Negative Nat accepted"); }
            catch (IllegalArgumentException expected) { }
            try { answer.apply(new HostileNat()); throw new AssertionError("BigInteger subclass accepted"); }
            catch (IllegalArgumentException expected) { }
            try { echo.apply("x".repeat(65537)); throw new AssertionError("Over-limit String accepted"); }
            catch (IllegalArgumentException expected) { }
            try { echo.apply("\uD800"); throw new AssertionError("Unpaired surrogate accepted"); }
            catch (IllegalArgumentException expected) { }
            require(answer.apply(BigInteger.TEN).equals(BigInteger.valueOf(21)), "Rejected arguments preserve Project");
            AtomicReference<Throwable> threadFailure = new AtomicReference<>();
            Thread other = new Thread(() -> {
                try { require(answer.apply(BigInteger.ONE).equals(BigInteger.valueOf(3)), "Serialized thread handoff"); }
                catch (Throwable failure) { threadFailure.set(failure); }
            });
            other.start(); other.join();
            if (threadFailure.get() != null) throw new AssertionError("Idle thread handoff failed", threadFailure.get());
            for (int i = 0; i < 2; i++) {
                MainResult result = project.runMain();
                require(result.stdout().equals("Hello, Lean/JVM\n") && result.stderr().isEmpty(), "Per-call captured IO Unit");
            }
            Object compiler = Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport"));
            require(compiler == null, "Artifact loading initialized source compiler");
            require(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("prototype.machine")) == null,
                    "Legacy prototype loaded");
            project.close(); project.close();
            try { retained.apply(BigInteger.ZERO); throw new AssertionError("Closed handle accepted"); }
            catch (IllegalStateException expected) { }
        }
        System.out.println("PASS exact Nat/String, repeated main, argument/type rejection, thread handoff, close; JVM-only application JAR");
    }
}
