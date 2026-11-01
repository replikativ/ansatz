package ansatz.lean.jvm;

import java.util.Objects;

/** Captured output of one successfully completed IO Unit entry. */
public final class MainResult {
    private final String stdout;
    private final String stderr;

    public MainResult(String stdout, String stderr) {
        this.stdout = Objects.requireNonNull(stdout, "stdout");
        this.stderr = Objects.requireNonNull(stderr, "stderr");
    }

    public String stdout() { return stdout; }
    public String stderr() { return stderr; }
}
