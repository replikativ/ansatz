import ansatz.lean.jvm.*;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.time.Duration;
import java.util.List;

/**
 * Service semantics through the packaged facade: per-call budgets, retirement
 * after an execution failure and in-place restart, native panic semantics and
 * the fail-on-panic policy, non-terminal returned IO errors, startup budgets.
 * Source: resources/lean/service-semantics-source/Svc.lean (Lean 4.33.1, v4 producer).
 */
public final class ServiceSemanticsSmoke {
    private static final String MANIFEST = "b7bae9deb07b329bc9fc85d6f174ccc6b6dc1ce16e443313a9a242ff105dabd1";
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static String code(Runnable call) {
        try { call.run(); return "none"; } catch (LeanException failure) { return failure.code(); }
    }
    private static LeanProject open(Lean runtime) throws java.io.IOException {
        return runtime.loadArtifact(ServiceSemanticsSmoke.class.getClassLoader(), "lean/service-semantics.zip", MANIFEST);
    }

    public static void main(String[] args) throws Exception {
        PrintStream original = System.err;
        ByteArrayOutputStream forwarded = new ByteArrayOutputStream();
        try (Lean runtime = Lean.open(); LeanProject project = open(runtime)) {
            LeanFunction count = project.function("Svc.count");
            check(count.invoke(1000).equals(n(499500)));
            // Default budget: two million instructions.
            check(code(() -> count.invoke(1_000_000)).equals("ResourceLimit"));
            check(project.isFailed());
            check(code(() -> count.invoke(3)).equals("ProjectFailed"));
            project.restart();
            check(!project.isFailed());
            check(count.invoke(3).equals(n(3)));
            InvocationOptions raised = InvocationOptions.empty().withBudget(1L << 33, Duration.ofMinutes(2));
            check(raised.instructionBudget() == 1L << 33 && raised.timeBudget().equals(Duration.ofMinutes(2)));
            check(count.invokeWith(raised, 1_000_000).equals(n(499_999_500_000L)));

            // Native panic semantics: message to stderr, default value returned, Project stays ready.
            System.setErr(new PrintStream(forwarded, true, StandardCharsets.UTF_8));
            try {
                check(project.function("Svc.pick").invoke(List.of(1, 2, 3), 7).equals(n(0)));
                check(project.function("Svc.boom").invoke(0).equals(n(0)));
            } finally { System.setErr(original); }
            check(forwarded.toString(StandardCharsets.UTF_8)
                  .equals("Error: index out of bounds\nPANIC at Svc.boom Svc:7:43: zero\n"));
            check(!project.isFailed());
            IOResult<?> loud = (IOResult<?>) project.call("Svc.loud", 0);
            check(loud.value().equals(n(0)) && loud.stdout().equals("loud 0\n"));
            check(loud.stderr().equals("PANIC at Svc.boom Svc:7:43: zero\n"));

            // Fail-on-panic mirrors LEAN_ABORT_ON_PANIC and retires the Project.
            check(code(() -> project.callWith("Svc.boom", InvocationOptions.empty().withFailOnPanic(true), 0))
                  .equals("LeanPanic"));
            check(project.isFailed());
            project.restart();

            // A returned IO error is a result, not an execution failure.
            check(code(() -> project.call("Svc.failing", 0)).equals("GuestIOError"));
            check(!project.isFailed());
            check(((IOResult<?>) project.call("Svc.failing", 5)).value().equals(n(5)));
        }
        try {
            InvocationOptions.empty().withBudget(0, Duration.ofSeconds(1));
            throw new AssertionError("zero budget accepted");
        } catch (IllegalArgumentException expected) { checks++; }
        HostServices tiny = HostServices.builder().startupBudget(10, Duration.ofSeconds(1)).build();
        try (Lean runtime = Lean.open(tiny)) {
            String startup = "none";
            try (LeanProject project = open(runtime)) { } catch (LeanException failure) { startup = failure.code(); }
            check(startup.equals("ResourceLimit"));
        }
        System.out.println("ServiceSemanticsSmoke checks=" + checks);
    }
}
