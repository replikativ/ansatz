package ansatz.lean.jvm;

import java.util.Objects;

/** Immutable explicit runtime service configuration, independent of source compilation. */
public final class HostServices {
    public static final class Builder {
        private ReadOnlyFiles files;
        private FileAccess fileAccess;
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
        public HostServices build() { return new HostServices(files, fileAccess); }
    }

    private final ReadOnlyFiles files;
    private final FileAccess fileAccess;
    private HostServices(ReadOnlyFiles files, FileAccess fileAccess) { this.files = files; this.fileAccess = fileAccess; }
    public static Builder builder() { return new Builder(); }
    /** Compatibility view for Builder.files(ReadOnlyFiles), otherwise null; use fileAccess for neutral policy. */
    public ReadOnlyFiles files() { return files; }
    /** Explicit immutable filesystem policy, or null when filesystem IO is unavailable. */
    public FileAccess fileAccess() { return fileAccess; }
}
