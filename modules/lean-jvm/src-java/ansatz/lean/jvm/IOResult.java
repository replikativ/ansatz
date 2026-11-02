package ansatz.lean.jvm;

/** A decoded successful IO value and its per-call captured output. */
public final class IOResult<T> {
    private final T value;
    private final String stdout;
    private final String stderr;

    public IOResult(T value, String stdout, String stderr) {
        this.value = value;
        this.stdout = java.util.Objects.requireNonNull(stdout, "stdout");
        this.stderr = java.util.Objects.requireNonNull(stderr, "stderr");
    }

    public T value() { return value; }
    public String stdout() { return stdout; }
    public String stderr() { return stderr; }
}
