package ansatz.lean.jvm;

import java.nio.file.Path;
import java.util.Objects;

/**
 * Immutable configuration for bounded regular files in a trusted Linux
 * namespace. The caller guarantees no hostile namespace replacement. Writable
 * sessions additionally require trusted aliases and no concurrent content mutation.
 * This is not a filesystem security sandbox. Construction performs no filesystem IO;
 * provider/platform/path checks and resource acquisition happen when used.
 */
public final class FileAccess {
    private final boolean writable;
    private final int maxWriteBytes;
    private final long maxTotalWriteBytes;
    private final Path root;
    private final Path workingDirectory;
    private final int maxHandles, maxReadBytes, maxPathBytes;
    private final long maxTotalBytes, maxOperations;

    private FileAccess(boolean writable, int maxWriteBytes, long maxTotalWriteBytes, Path root, Path workingDirectory, int maxHandles, int maxReadBytes,
                          long maxTotalBytes, long maxOperations, int maxPathBytes) {
        this.writable = writable; this.maxWriteBytes = maxWriteBytes; this.maxTotalWriteBytes = maxTotalWriteBytes;
        this.root = root;
        this.workingDirectory = workingDirectory;
        if (maxWriteBytes < 1 || maxWriteBytes > 16 * 1024 * 1024 || maxTotalWriteBytes < 0 || maxHandles < 1 || maxHandles > 1024 || maxReadBytes < 1 || maxReadBytes > 16 * 1024 * 1024
                || maxTotalBytes < 0 || maxOperations < 1 || maxPathBytes < 1 || maxPathBytes > 1048576)
            throw new IllegalArgumentException("Unsupported filesystem limits");
        this.maxHandles = maxHandles;
        this.maxReadBytes = maxReadBytes;
        this.maxTotalBytes = maxTotalBytes;
        this.maxOperations = maxOperations;
        this.maxPathBytes = maxPathBytes;
    }

    /** Capture an explicit host root without opening it or requiring it to exist. */
    public static FileAccess readOnly(Path root) {
        Path absolute = Objects.requireNonNull(root, "root").toAbsolutePath().normalize();
        return new FileAccess(false, 1048576, 16L * 1048576, absolute, absolute.getFileSystem().getPath("."),
                32, 1048576, 16L * 1048576, 10000, 4096);
    }

    /** Return a new configuration with a guest directory relative to the root. */
    public FileAccess workingDirectory(Path relative) {
        Objects.requireNonNull(relative, "relative");
        if (relative.isAbsolute() || relative.getFileSystem() != root.getFileSystem())
            throw new IllegalArgumentException("Guest working directory must be relative to the configured root");
        for (Path component : relative) {
            if (component.toString().equals(".."))
                throw new IllegalArgumentException("Parent components are outside the filesystem profile");
        }
        return new FileAccess(writable, maxWriteBytes, maxTotalWriteBytes, root, relative, maxHandles, maxReadBytes, maxTotalBytes, maxOperations, maxPathBytes);
    }

    /** Return a new configuration; total bytes include provider read-ahead. */
    public FileAccess limits(int maxHandles, int maxReadBytes, long maxTotalBytes,
                               long maxOperations, int maxPathBytes) {
        return new FileAccess(writable, maxWriteBytes, maxTotalWriteBytes, root, workingDirectory, maxHandles, maxReadBytes,
                maxTotalBytes, maxOperations, maxPathBytes);
    }

    /** Explicitly permit regular-file mutation in a trusted namespace and trusted aliases. */
    public static FileAccess readWrite(Path root) {
        FileAccess config = readOnly(root);
        return new FileAccess(true, config.maxWriteBytes, config.maxTotalWriteBytes, config.root,
                config.workingDirectory, config.maxHandles, config.maxReadBytes, config.maxTotalBytes,
                config.maxOperations, config.maxPathBytes);
    }
    /** Physical writes are counted separately from read-ahead. Limits never imply rollback. */
    public FileAccess writeLimits(int perWriteBytes, long totalWriteBytes) {
        return new FileAccess(writable, perWriteBytes, totalWriteBytes, root, workingDirectory,
                maxHandles, maxReadBytes, maxTotalBytes, maxOperations, maxPathBytes);
    }
    public boolean writable() { return writable; }
    public int maxWriteBytes() { return maxWriteBytes; }
    public long maxTotalWriteBytes() { return maxTotalWriteBytes; }

    public Path root() { return root; }
    public Path workingDirectory() { return workingDirectory; }
    public int maxHandles() { return maxHandles; }
    public int maxReadBytes() { return maxReadBytes; }
    public long maxTotalBytes() { return maxTotalBytes; }
    public long maxOperations() { return maxOperations; }
    public int maxPathBytes() { return maxPathBytes; }
}
