package ansatz.lean.jvm.internal.fs;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InterruptedIOException;
import java.nio.ByteBuffer;
import java.nio.channels.ClosedByInterruptException;
import java.nio.channels.FileChannel;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.nio.file.AccessDeniedException;
import java.nio.file.FileSystemLoopException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.NoSuchFileException;
import java.nio.file.NotDirectoryException;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.FileTime;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Bounded Linux/default-provider regular-file sessions in an explicitly trusted
 * namespace. The caller guarantees no concurrent path/symlink replacement.
 * Component checks are restrictions, not a race-safe security sandbox. File
 * contents are live, not snapshots. No guest values, errno tags, or engine live
 * here. Calls are synchronous; cancellation is cooperative around provider IO.
 */
public final class ReadOnlyFileSession implements AutoCloseable {
    private static final LinkOption[] NOFOLLOW = {LinkOption.NOFOLLOW_LINKS};
    private static final String ATTRIBUTES = "unix:lastAccessTime,lastModifiedTime,size,nlink,mode";
    private static final int TYPE_MASK = 0170000, REGULAR = 0100000, DIRECTORY = 0040000, SYMLINK = 0120000;
    public enum Operation { CONFIGURE, METADATA, OPEN, READ, GET_LINE, WRITE, PUT_STR, FLUSH, IS_TTY }
    public enum Code { RESOURCE_LIMIT, CANCELLED, PROVIDER_FAILURE, POLICY, INVALID_HANDLE, CLOSED }
    public enum FileKind { DIRECTORY, REGULAR, OTHER }
    public record Limits(int maxHandles, int maxReadBytes, long maxTotalBytes, long maxOperations, int maxPathBytes) {
        public Limits {
            if (maxHandles < 1 || maxHandles > 1024 || maxReadBytes < 1 || maxReadBytes > 16 * 1024 * 1024
                    || maxTotalBytes < 0 || maxOperations < 1 || maxPathBytes < 1 || maxPathBytes > 1048576)
                throw new IllegalArgumentException("Unsupported filesystem limits");
        }
    }
    public record Timestamp(long seconds, int nanoseconds) {}
    public record Metadata(Timestamp accessed, Timestamp modified, long size, long links, FileKind kind, int mode) {}
    public record Stats(long operations, long bytesRead, long opened, long closeAttempts, int liveHandles,
                        boolean closed, Code terminalCode, List<String> closeDiagnostics) {}
    /** Positive Linux errno facts only; the engine owns IO.Error/negative-UV encoding. */
    public static final class FSFailure extends Exception {
        private final Operation operation;
        private final int errno;
        private final String path;
        private FSFailure(Operation operation, int errno, String path, String message, IOException cause) {
            super(message, cause); this.operation = operation; this.errno = errno; this.path = path;
        }
        public Operation operation() { return operation; }
        public int errno() { return errno; }
        public String path() { return path; }
    }
    public static final class Terminal extends RuntimeException {
        private final Code code;
        private Terminal(Code code, String message, Throwable cause) { super(message, cause); this.code = code; }
        public Code code() { return code; }
    }
    /** Token identity belongs to exactly one session; no channel is exposed. */
    public static final class Handle implements AutoCloseable {
        private final ReadOnlyFileSession owner;
        private final long id;
        private boolean closed;
        private Handle(ReadOnlyFileSession owner, long id) { this.owner = owner; this.id = id; }
        public long id() { return id; }
        public boolean isClosed() { synchronized (owner) { return closed; } }
        @Override public void close() { owner.closeHandle(this); }
    }
    @FunctionalInterface interface Opener { FileChannel open(Path path) throws IOException; }
    private static final class Entry {
        final Handle handle;
        final ByteBuffer buffered = ByteBuffer.allocate(8192);
        FileChannel channel;
        boolean closeClaimed, fileError;
        Entry(Handle handle) { this.handle = handle; buffered.limit(0); }
    }
    private final Path root, cwd;
    private final Limits limits;
    private final Opener opener;
    private final Map<Long, Entry> live = new LinkedHashMap<>();
    private final List<String> closeDiagnostics = new ArrayList<>();
    private long operations, bytesRead, opened, closeAttempts, nextId = 1;
    private boolean closed;
    private Terminal terminal;
    // A plain identity token only: never an engine/guest/resource back-reference.
    private Object claimedOwner;

    /** Bind this fresh session to one engine exactly once. Refusal is read-only:
     * it neither poisons the existing owner nor changes resource/operation state.
     */
    public synchronized void claimOwner(Object token) {
        if (token == null || token.getClass() != Object.class)
            throw new IllegalArgumentException("An inert engine identity token is required");
        if (claimedOwner != null || closed || terminal != null || operations != 0 || bytesRead != 0
                || opened != 0 || closeAttempts != 0 || nextId != 1 || !live.isEmpty())
            throw new IllegalStateException("Filesystem session must be fresh and unclaimed");
        claimedOwner = token;
    }

    public ReadOnlyFileSession(Path root, Path guestWorkingDirectory, Limits limits) throws FSFailure {
        this(root, guestWorkingDirectory, limits, path -> FileChannel.open(path, StandardOpenOption.READ));
    }
    // Test seam, package-private: alternate channels cannot select another path resolver.
    ReadOnlyFileSession(Path root, Path guestWorkingDirectory, Limits limits, Opener opener) throws FSFailure {
        this.limits = Objects.requireNonNull(limits); this.opener = Objects.requireNonNull(opener);
        Objects.requireNonNull(root); Objects.requireNonNull(guestWorkingDirectory);
        if (!System.getProperty("os.name", "").equals("Linux") || root.getFileSystem() != FileSystems.getDefault()
                || guestWorkingDirectory.getFileSystem() != FileSystems.getDefault())
            throw fail(Code.POLICY, "Only the trusted Linux default filesystem provider is supported", null);
        this.root = root.toAbsolutePath().normalize();
        try {
            // Include ancestors of the supplied root, not just guest components.
            Path current = this.root.getRoot();
            for (Path component : this.root) {
                current = current.resolve(component);
                Metadata metadata = attributes(current, Operation.CONFIGURE, null);
                if (metadata.kind() != FileKind.DIRECTORY)
                    throw fail(Code.POLICY, "Filesystem root must be a directory", null);
            }
            this.cwd = resolveFrom(this.root, guestWorkingDirectory.toString(), Operation.CONFIGURE, true);
            if (attributes(cwd, Operation.CONFIGURE, null).kind() != FileKind.DIRECTORY)
                throw fail(Code.POLICY, "Guest working directory must be a directory", null);
            poll();
        } catch (IOException failure) { throw translate(Operation.CONFIGURE, null, failure); }
    }
    private Terminal fail(Code code, String message, Throwable cause) {
        if (terminal == null) terminal = new Terminal(code, message, cause);
        return terminal;
    }
    private void poll() {
        if (Thread.currentThread().isInterrupted()) throw fail(Code.CANCELLED, "Filesystem operation interrupted", null);
    }
    private void begin() {
        if (closed) throw new Terminal(Code.CLOSED, "Filesystem session is closed", null);
        if (terminal != null) throw terminal;
        poll();
        if (operations == limits.maxOperations()) throw fail(Code.RESOURCE_LIMIT, "Filesystem operation limit", null);
        operations++;
    }
    private FSFailure guest(Operation operation, int errno, String path, String message) {
        return new FSFailure(operation, errno, path, message, null);
    }
    private FSFailure translate(Operation operation, String path, IOException failure) {
        if (failure instanceof ClosedByInterruptException || failure instanceof InterruptedIOException) {
            Thread.currentThread().interrupt();
            throw fail(Code.CANCELLED, "Filesystem provider interrupted", failure);
        }
        if (Thread.currentThread().isInterrupted()) throw fail(Code.CANCELLED, "Filesystem operation interrupted", failure);
        int errno;
        if (failure instanceof NoSuchFileException) errno = 2;
        else if (failure instanceof AccessDeniedException) errno = 13;
        else if (failure instanceof NotDirectoryException) errno = 20;
        else if (failure instanceof FileSystemLoopException) errno = 40;
        else throw fail(Code.PROVIDER_FAILURE, "Unclassified filesystem IOException", failure);
        return new FSFailure(operation, errno, path, failure.getClass().getSimpleName(), failure);
    }
    private Path resolveFrom(Path base, String guest, Operation operation, boolean allowEmpty) throws FSFailure, IOException {
        Objects.requireNonNull(guest);
        if (guest.length() > limits.maxPathBytes()) throw fail(Code.RESOURCE_LIMIT, "Filesystem path byte limit", null);
        try {
            int bytes = StandardCharsets.UTF_8.newEncoder().onMalformedInput(CodingErrorAction.REPORT)
                    .onUnmappableCharacter(CodingErrorAction.REPORT).encode(java.nio.CharBuffer.wrap(guest)).remaining();
            if (bytes > limits.maxPathBytes()) throw fail(Code.RESOURCE_LIMIT, "Filesystem path byte limit", null);
        } catch (CharacterCodingException failure) { throw fail(Code.POLICY, "Invalid Unicode path", failure); }
        if (guest.indexOf('\0') >= 0) throw guest(operation, 22, guest, "Path contains NUL");
        if (guest.isEmpty() && !allowEmpty) throw guest(operation, 2, guest, "Empty path");
        Path relative = Path.of(guest);
        if (relative.isAbsolute()) throw fail(Code.POLICY, "Absolute guest path is outside this profile", null);
        for (Path part : relative) if (part.toString().equals(".."))
            throw fail(Code.POLICY, "Parent path components are outside this profile", null);
        Path resolved = base.resolve(relative).normalize();
        if (!resolved.startsWith(root)) throw fail(Code.POLICY, "Guest path escapes the configured root", null);
        Path current = root;
        List<Path> components = new ArrayList<>(); root.relativize(resolved).forEach(components::add);
        for (int i = 0; i < components.size(); i++) {
            current = current.resolve(components.get(i));
            Metadata metadata = attributes(current, operation, guest);
            if (i + 1 < components.size() && metadata.kind() != FileKind.DIRECTORY)
                throw guest(operation, 20, guest, "Path ancestor is not a directory");
        }
        return resolved;
    }
    // Package-private only for exact-domain tests; provider values use this same path.
    Timestamp timestamp(Object value) {
        if (!(value instanceof FileTime time)) throw fail(Code.PROVIDER_FAILURE, "Missing unix file timestamp", null);
        Instant instant = time.toInstant();
        // The Unix JDK provider can already have rounded native nanos to micros
        // outside its signed-long nanosecond range. FileTime round-trip alone
        // cannot detect that loss. Restrict seconds before trusting its fraction.
        if (instant.getEpochSecond() < -9_223_372_036L || instant.getEpochSecond() > 9_223_372_035L
                || !FileTime.from(instant).equals(time))
            throw fail(Code.PROVIDER_FAILURE, "Timestamp outside exact supported range", null);
        return new Timestamp(instant.getEpochSecond(), instant.getNano());
    }
    private Metadata attributes(Path path, Operation operation, String guest) throws IOException {
        poll();
        Map<String, Object> attrs;
        try { attrs = Files.readAttributes(path, ATTRIBUTES, NOFOLLOW); }
        catch (UnsupportedOperationException failure) { throw fail(Code.POLICY, "Unix filesystem attributes unavailable", failure); }
        poll();
        Object size = attrs.get("size"), links = attrs.get("nlink"), mode = attrs.get("mode");
        if (!(size instanceof Long) || (Long) size < 0 || !(links instanceof Integer) || (Integer) links < 0
                || !(mode instanceof Integer))
            throw fail(Code.PROVIDER_FAILURE, "Unix attribute value outside truthful supported range", null);
        int bits = (Integer) mode;
        if ((bits & ~0177777) != 0) throw fail(Code.PROVIDER_FAILURE, "Unix mode outside supported bit range", null);
        if ((bits & TYPE_MASK) == SYMLINK) throw fail(Code.POLICY, "Symlinks are outside this filesystem profile", null);
        FileKind kind = (bits & TYPE_MASK) == REGULAR ? FileKind.REGULAR
                : (bits & TYPE_MASK) == DIRECTORY ? FileKind.DIRECTORY : FileKind.OTHER;
        return new Metadata(timestamp(attrs.get("lastAccessTime")), timestamp(attrs.get("lastModifiedTime")),
                (Long) size, ((Integer) links).longValue(), kind, bits);
    }
    public synchronized Metadata metadata(String guest) throws FSFailure {
        begin();
        try { Metadata result = attributes(resolveFrom(cwd, guest, Operation.METADATA, false), Operation.METADATA, guest); poll(); return result; }
        catch (IOException failure) { throw translate(Operation.METADATA, guest, failure); }
    }
    public synchronized Handle open(String guest) throws FSFailure {
        begin();
        if (live.size() >= limits.maxHandles()) throw fail(Code.RESOURCE_LIMIT, "Open file handle limit", null);
        if (nextId == Long.MAX_VALUE) throw fail(Code.RESOURCE_LIMIT, "File handle identity limit", null);
        Entry entry = new Entry(new Handle(this, nextId++));
        try {
            Path path = resolveFrom(cwd, guest, Operation.OPEN, false);
            FileKind kind = attributes(path, Operation.OPEN, guest).kind();
            if (kind != FileKind.REGULAR) throw fail(Code.POLICY, "Only regular files may be opened", null);
            poll();
            // Publish provisional custody before an OS resource can be acquired.
            // Map allocation failure therefore happens before opener.open.
            live.put(entry.handle.id, entry);
            entry.channel = opener.open(path); opened++;
            if (entry.channel == null || !entry.channel.isOpen()) throw fail(Code.PROVIDER_FAILURE, "Provider returned a closed file", null);
            poll(); return entry.handle;
        } catch (IOException failure) {
            if (entry.channel == null) live.remove(entry.handle.id);
            throw translate(Operation.OPEN, guest, failure);
        }
        catch (RuntimeException | Error failure) {
            if (!(failure instanceof Terminal)) fail(Code.PROVIDER_FAILURE, "Unexpected filesystem provider failure", failure);
            if (entry.channel != null) {
                try { retire(entry); }
                catch (RuntimeException | Error secondary) {
                    if (higherPriority(secondary, failure)) throw secondary;
                    try { diagnostic(secondary); }
                    catch (RuntimeException | Error diagnosticFailure) {
                        if (higherPriority(diagnosticFailure, failure)) throw diagnosticFailure;
                    }
                }
            } else live.remove(entry.handle.id);
            throw failure;
        }
    }
    private Entry entry(Handle handle) {
        if (handle == null || handle.owner != this || handle.closed || live.get(handle.id) == null
                || live.get(handle.id).handle != handle)
            throw fail(Code.INVALID_HANDLE, "Foreign or stale file handle", null);
        return live.get(handle.id);
    }
    private int readChannel(Entry entry, ByteBuffer buffer, Operation operation) throws FSFailure {
        poll();
        long available = limits.maxTotalBytes() - bytesRead;
        if (available == 0) throw fail(Code.RESOURCE_LIMIT, "Filesystem total read byte limit", null);
        int oldLimit = buffer.limit();
        buffer.limit(buffer.position() + (int) Math.min(buffer.remaining(), available));
        try {
            int count = entry.channel.read(buffer);
            if (count == 0) throw fail(Code.PROVIDER_FAILURE, "Regular file read made no progress", null);
            if (count > 0) bytesRead += count;
            poll(); return count;
        } catch (IOException failure) {
            entry.fileError = true;
            throw translate(operation, null, failure);
        }
        catch (RuntimeException | Error failure) {
            if (!(failure instanceof Terminal)) fail(Code.PROVIDER_FAILURE, "Unexpected filesystem read failure", failure);
            throw failure;
        }
        finally { buffer.limit(oldLimit); }
    }
    public synchronized byte[] read(Handle handle, long count) throws FSFailure {
        begin(); Entry entry = entry(handle);
        if (count < 0 || count > limits.maxReadBytes()) throw fail(Code.RESOURCE_LIMIT, "Filesystem per-read byte limit", null);
        if (count > limits.maxTotalBytes() - bytesRead + entry.buffered.remaining())
            throw fail(Code.RESOURCE_LIMIT, "Filesystem total read byte limit", null);
        byte[] result = new byte[(int) count]; int used = Math.min(result.length, entry.buffered.remaining());
        entry.buffered.get(result, 0, used);
        ByteBuffer output = ByteBuffer.wrap(result); output.position(used);
        boolean eof = false;
        while (output.hasRemaining()) {
            if (readChannel(entry, output, Operation.READ) < 0) { eof = true; break; }
        }
        // Pinned Handle.read clears FILE indicators only for an empty EOF
        // result. A zero-sized request and a positive short read do not clear.
        if (eof && output.position() == 0) entry.fileError = false;
        poll(); return output.position() == result.length ? result : Arrays.copyOf(result, output.position());
    }
    /** Raw bytes include LF and preserve CR/NUL/invalid UTF-8; engine decoding is separate. */
    public synchronized byte[] getLine(Handle handle) throws FSFailure {
        begin(); Entry entry = entry(handle);
        // Native getLine consults sticky ferror even after successful getc,
        // then decodes ambient errno. The JVM cannot recover that thread-local
        // native errno faithfully. Refuse this state before consuming any line
        // instead of inventing EBADF or silently returning a successful value.
        if (entry.fileError)
            throw fail(Code.POLICY, "getLine after a sticky FILE error is outside the errno profile", null);
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        while (true) {
            if (!entry.buffered.hasRemaining()) {
                entry.buffered.clear();
                int read = readChannel(entry, entry.buffered, Operation.GET_LINE);
                entry.buffered.flip(); if (read < 0) break;
            }
            if (output.size() == limits.maxReadBytes()) throw fail(Code.RESOURCE_LIMIT, "Filesystem line byte limit", null);
            int value = Byte.toUnsignedInt(entry.buffered.get()); output.write(value);
            if (value == '\n') break;
        }
        poll(); return output.toByteArray();
    }
    /** POSIX seekable-input fflush: discard prefetch and synchronize descriptor offset. */
    public synchronized void flush(Handle handle) throws FSFailure {
        begin(); Entry entry = entry(handle);
        try {
            long logical = entry.channel.position() - entry.buffered.remaining(); poll();
            entry.channel.position(logical); entry.buffered.limit(0);
            poll();
        } catch (IOException failure) { throw translate(Operation.FLUSH, null, failure); }
    }
    public synchronized boolean isTty(Handle handle) { begin(); entry(handle); poll(); return false; }
    public synchronized void write(Handle handle, byte[] bytes) throws FSFailure {
        begin(); Entry entry = entry(handle); Objects.requireNonNull(bytes);
        if (bytes.length == 0) return;
        entry.fileError = true;
        throw guest(Operation.WRITE, 9, null, "Read-only file policy forbids write");
    }
    public synchronized void putStr(Handle handle, String text) throws FSFailure {
        begin(); Entry entry = entry(handle); Objects.requireNonNull(text);
        if (text.isEmpty()) return;
        entry.fileError = true;
        throw guest(Operation.PUT_STR, 9, null, "Read-only file policy forbids putStr");
    }
    private void diagnostic(Throwable failure) {
        if (closeDiagnostics.size() < 8) closeDiagnostics.add(failure.getClass().getName());
    }
    private void retire(Entry entry) {
        if (entry.closeClaimed) return; // an uncertain close must never replay
        if (entry.channel == null) {
            // A failed acquisition published no resource or guest handle.
            entry.handle.closed = true; live.remove(entry.handle.id); return;
        }
        entry.closeClaimed = true; entry.handle.closed = true; closeAttempts++;
        try {
            entry.channel.close();
            // AbstractInterruptibleChannel marks itself closed before its
            // implementation runs: isOpen()==false is not a retirement proof.
            live.remove(entry.handle.id);
        } catch (IOException failure) {
            // Native-style RC finalization does not throw an IO exception, but
            // uncertain resource custody stays live for the session certificate.
            diagnostic(failure);
        }
    }
    private synchronized void closeHandle(Handle handle) {
        if (handle.owner != this) throw fail(Code.INVALID_HANDLE, "Foreign handle close", null);
        if (!handle.closed) retire(entry(handle));
    }
    private static boolean higherPriority(Throwable candidate, Throwable primary) {
        return primary == null || candidate instanceof Error && !(primary instanceof Error)
                || (candidate instanceof VirtualMachineError || candidate instanceof ThreadDeath)
                   && !(primary instanceof VirtualMachineError) && !(primary instanceof ThreadDeath);
    }
    @Override public synchronized void close() {
        if (closed && live.isEmpty()) return;
        // An allocation failure leaves the prior closed flag and every entry
        // unchanged; later cleanup may still attempt all unclaimed resources.
        List<Entry> pending = new ArrayList<>(live.values());
        closed = true; Throwable fatal = null;
        for (Entry entry : pending) {
            try { retire(entry); }
            catch (RuntimeException | Error failure) {
                if (higherPriority(failure, fatal)) fatal = failure;
            }
        }
        if (fatal instanceof Error error) throw error;
        if (fatal instanceof RuntimeException failure) throw failure;
        if (!live.isEmpty()) {
            Terminal uncertain = new Terminal(Code.PROVIDER_FAILURE, "Filesystem close left uncertain resource custody", null);
            if (terminal == null) terminal = uncertain;
            throw uncertain;
        }
    }
    public synchronized Stats stats() {
        return new Stats(operations, bytesRead, opened, closeAttempts, live.size(), closed,
                terminal == null ? null : terminal.code(), List.copyOf(closeDiagnostics));
    }
}
