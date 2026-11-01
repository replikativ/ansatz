package ansatz.lean.jvm;

import java.nio.file.Path;
import java.util.Objects;

/** Explicit trusted native installation and separately supplied producer bundle. */
public final class NativeCompilerOptions {
    private final Path sysroot;
    private final Path producerBundle;
    private final Path cache;

    public NativeCompilerOptions(Path sysroot, Path producerBundle, Path cache) {
        this.sysroot = Objects.requireNonNull(sysroot, "sysroot");
        this.producerBundle = Objects.requireNonNull(producerBundle, "producerBundle");
        this.cache = Objects.requireNonNull(cache, "cache");
    }

    public String compatibilityProfile() { return "lean-native-local-init-dag/1"; }
    public Path sysroot() { return sysroot; }
    public Path producerBundle() { return producerBundle; }
    public Path cache() { return cache; }
}
