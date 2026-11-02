package ansatz.lean.jvm;

/** A decoded successful IO value and its per-call captured output. */
public final class IOResult<T> {
    private final T value;
    private final String stdout;
    private final String stderr;
    private final byte[] stdoutBytes;
    private final byte[] stderrBytes;

    public IOResult(T value, String stdout, String stderr) {
        this.value = value;
        this.stdout = java.util.Objects.requireNonNull(stdout, "stdout");
        this.stderr = java.util.Objects.requireNonNull(stderr, "stderr");
        this.stdoutBytes = stdout.getBytes(java.nio.charset.StandardCharsets.UTF_8);
        this.stderrBytes = stderr.getBytes(java.nio.charset.StandardCharsets.UTF_8);
    }

    /** Byte captures are authoritative; text views replace malformed UTF-8. */
    public IOResult(T value, byte[] stdout, byte[] stderr) {
        this.value = value;
        this.stdoutBytes = java.util.Objects.requireNonNull(stdout, "stdout").clone();
        this.stderrBytes = java.util.Objects.requireNonNull(stderr, "stderr").clone();
        this.stdout = new String(stdoutBytes, java.nio.charset.StandardCharsets.UTF_8);
        this.stderr = new String(stderrBytes, java.nio.charset.StandardCharsets.UTF_8);
    }

    public T value() { return value; }
    public String stdout() { return stdout; }
    public String stderr() { return stderr; }
    public byte[] stdoutBytes() { return stdoutBytes.clone(); }
    public byte[] stderrBytes() { return stderrBytes.clone(); }
}
