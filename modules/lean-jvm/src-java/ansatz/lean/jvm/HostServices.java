package ansatz.lean.jvm;

import java.time.Duration;
import java.util.Objects;

/**
 * Immutable explicit runtime service configuration of one {@link Lean} scope,
 * independent of source compilation: filesystem policy and the cooperative
 * budget of Project startup (module initialization), including restarts.
 */
public final class HostServices {
    public static final class Builder {
        private ReadOnlyFiles files;
        private FileAccess fileAccess;
        private long startupInstructions = InvocationOptions.DEFAULT_INSTRUCTIONS;
        private long startupNanos = InvocationOptions.DEFAULT_TIME.toNanos();
        private Builder() {}
        public Builder files(ReadOnlyFiles files) {
            this.files = Objects.requireNonNull(files, "files");
            this.fileAccess = files.fileAccess();
            return this;
        }
        public Builder fileAccess(FileAccess files) {
            this.fileAccess = Objects.requireNonNull(files, "files");
            this.files = null;
            return this;
        }
        /** Budget for initializing each loaded or restarted Project; same bounds as a call budget. */
        public Builder startupBudget(long instructions, Duration time) {
            long nanos = InvocationOptions.nanos(time);
            InvocationOptions.checkBudget(instructions, nanos);
            this.startupInstructions = instructions;
            this.startupNanos = nanos;
            return this;
        }
        public HostServices build() { return new HostServices(files, fileAccess, startupInstructions, startupNanos); }
    }

    private final ReadOnlyFiles files;
    private final FileAccess fileAccess;
    private final long startupInstructions;
    private final long startupNanos;
    private HostServices(ReadOnlyFiles files, FileAccess fileAccess, long startupInstructions, long startupNanos) {
        this.files = files; this.fileAccess = fileAccess;
        this.startupInstructions = startupInstructions; this.startupNanos = startupNanos;
    }
    public static Builder builder() { return new Builder(); }
    /** Compatibility view for Builder.files(ReadOnlyFiles), otherwise null; use fileAccess for neutral policy. */
    public ReadOnlyFiles files() { return files; }
    /** Explicit immutable filesystem policy, or null when filesystem IO is unavailable. */
    public FileAccess fileAccess() { return fileAccess; }
    public long startupInstructionBudget() { return startupInstructions; }
    public Duration startupTimeBudget() { return Duration.ofNanos(startupNanos); }
    public long startupTimeBudgetNanos() { return startupNanos; }
}
