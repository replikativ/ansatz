import ansatz.lean.LeanRuntime;
import clojure.lang.IFn;
import java.util.Collections;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicBoolean;

/** Thin provider forwarding plus deliberate unchecked-input rejection, not frontend acceptance. */
public final class CompilerSmoke {
    public static void verify(IFn selectedRawConsumer) {
        AtomicInteger calls = new AtomicInteger();
        AtomicBoolean compiled = new AtomicBoolean(false);
        LeanRuntime.OpenOptions requested = new LeanRuntime.OpenOptions(
            Collections.singletonMap("profile", "typed-compiler"));
        try {
            LeanRuntime.open(options -> {
                if (options != requested) throw new AssertionError("provider options changed");
                calls.incrementAndGet();
                if (!"55".equals(selectedRawConsumer.invoke(options).toString()))
                    throw new AssertionError("compiled raw execution in provider");
                compiled.set(true);
                return new LeanRuntime.PreparedInput(Collections.emptyMap(), Collections.emptyMap(), new Object());
            }, requested);
            throw new AssertionError("Unchecked provider must reject");
        } catch (LeanRuntime.LeanException expected) {
            if (expected.failure() == null || expected.getCause() == null || calls.get() != 1 || !compiled.get())
                throw new AssertionError("provider failure/once-only evidence");
        }
        System.out.println("optional-compiler-java-provider-smoke-passed");
    }
}
