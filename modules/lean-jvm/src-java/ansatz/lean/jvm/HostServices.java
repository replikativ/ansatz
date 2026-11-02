package ansatz.lean.jvm;

import java.util.Objects;

/** Immutable explicit runtime service configuration, independent of source compilation. */
public final class HostServices {
    public static final class Builder {
        private ReadOnlyFiles files;
        private Builder() {}
        public Builder files(ReadOnlyFiles files) {
            this.files = Objects.requireNonNull(files, "files");
            return this;
        }
        public HostServices build() { return new HostServices(files); }
    }

    private final ReadOnlyFiles files;
    private HostServices(ReadOnlyFiles files) { this.files = files; }
    public static Builder builder() { return new Builder(); }
    /** The configured read-only filesystem, or null when no filesystem is permitted. */
    public ReadOnlyFiles files() { return files; }
}
