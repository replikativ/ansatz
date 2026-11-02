package ansatz.lean.jvm.internal.fs;

import java.io.IOException;
import java.io.InterruptedIOException;
import java.nio.ByteBuffer;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.nio.file.AccessDeniedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.FileTime;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/** Actual local channels; injected failures test ownership, not native errno parity. */
public final class ReadOnlyFileSessionChecks {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    @FunctionalInterface interface Action { void run() throws Exception; }
    private static ReadOnlyFileSession.Terminal terminal(ReadOnlyFileSession.Code code, Action action) throws Exception {
        try { action.run(); throw new AssertionError("Expected terminal " + code); }
        catch (ReadOnlyFileSession.Terminal failure) { check(failure.code() == code); return failure; }
    }
    private static void guest(int errno, ReadOnlyFileSession.Operation operation, Action action) throws Exception {
        try { action.run(); throw new AssertionError("Expected guest failure"); }
        catch (ReadOnlyFileSession.FSFailure failure) { check(failure.errno() == errno); check(failure.operation() == operation); }
    }
    private static ReadOnlyFileSession.Limits limits(int handles, int read, long total, long operations) {
        return new ReadOnlyFileSession.Limits(handles, read, total, operations, 4096);
    }
    private static ReadOnlyFileSession session(Path root) throws Exception {
        return new ReadOnlyFileSession(root, Path.of("."), limits(4, 65536, 1048576, 1000));
    }
    private static final class CountedChannel extends FileChannel {
        final FileChannel delegate;
        int closes;
        boolean interruptAfterRead, closeFailureBeforeDelegate;
        IOException readFailure, closeFailure;
        Error readError, closeError;
        CountedChannel(Path path) throws IOException { delegate = FileChannel.open(path, StandardOpenOption.READ); }
        @Override public int read(ByteBuffer bytes) throws IOException {
            if (readError != null) throw readError;
            if (readFailure != null) throw readFailure;
            int result = delegate.read(bytes);
            if (interruptAfterRead) Thread.currentThread().interrupt();
            return result;
        }
        @Override protected void implCloseChannel() throws IOException {
            closes++;
            if (closeFailureBeforeDelegate) {
                if (closeError != null) throw closeError;
                if (closeFailure != null) throw closeFailure;
            }
            delegate.close();
            if (closeError != null) throw closeError;
            if (closeFailure != null) throw closeFailure;
        }
        @Override public long position() throws IOException { return delegate.position(); }
        @Override public FileChannel position(long offset) throws IOException { delegate.position(offset); return this; }
        @Override public long size() throws IOException { return delegate.size(); }
        @Override public long read(ByteBuffer[] b, int o, int n) throws IOException { return delegate.read(b, o, n); }
        @Override public int read(ByteBuffer b, long p) throws IOException { return delegate.read(b, p); }
        @Override public int write(ByteBuffer b) throws IOException { return delegate.write(b); }
        @Override public long write(ByteBuffer[] b, int o, int n) throws IOException { return delegate.write(b, o, n); }
        @Override public int write(ByteBuffer b, long p) throws IOException { return delegate.write(b, p); }
        @Override public FileChannel truncate(long n) throws IOException { delegate.truncate(n); return this; }
        @Override public void force(boolean m) throws IOException { delegate.force(m); }
        @Override public long transferTo(long p, long n, WritableByteChannel c) throws IOException { return delegate.transferTo(p, n, c); }
        @Override public long transferFrom(ReadableByteChannel c, long p, long n) throws IOException { return delegate.transferFrom(c, p, n); }
        @Override public MappedByteBuffer map(MapMode m, long p, long n) throws IOException { return delegate.map(m, p, n); }
        @Override public FileLock lock(long p, long n, boolean shared) throws IOException { return delegate.lock(p, n, shared); }
        @Override public FileLock tryLock(long p, long n, boolean shared) throws IOException { return delegate.tryLock(p, n, shared); }
    }
    private static void claimRefused(ReadOnlyFileSession files, Object owner) {
        ReadOnlyFileSession.Stats before = files.stats();
        try { files.claimOwner(owner); throw new AssertionError("Session claim accepted"); }
        catch (IllegalArgumentException | IllegalStateException expected) { checks++; }
        check(before.equals(files.stats()));
    }
    private static void ownerAndTimestampDomains(Path root) throws Exception {
        Object owner = new Object();
        try (ReadOnlyFileSession fresh = session(root)) {
            claimRefused(fresh, null); claimRefused(fresh, "not an inert identity");
            check(fresh.stats().operations() == 0 && fresh.stats().opened() == 0);
            fresh.claimOwner(owner);
            claimRefused(fresh, owner); claimRefused(fresh, new Object());
            // Rejected second claims do not poison the already bound session.
            check(fresh.metadata(".").kind() == ReadOnlyFileSession.FileKind.DIRECTORY);
        }
        try (ReadOnlyFileSession used = session(root)) {
            used.metadata("."); claimRefused(used, new Object());
        }
        try (ReadOnlyFileSession used = session(root)) {
            ReadOnlyFileSession.Handle handle = used.open("data"); handle.close();
            check(used.stats().liveHandles() == 0); claimRefused(used, new Object());
        }
        ReadOnlyFileSession closed = session(root); closed.close(); claimRefused(closed, new Object());
        try (ReadOnlyFileSession failed = session(root)) {
            terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, () -> failed.timestamp("not a FileTime"));
            claimRefused(failed, new Object());
        }
        try (ReadOnlyFileSession exact = session(root)) {
            for (long seconds : new long[]{-9_223_372_036L,-3,0,9_223_372_035L}) {
                FileTime time = FileTime.from(Instant.ofEpochSecond(seconds,999_999_999));
                ReadOnlyFileSession.Timestamp value = exact.timestamp(time);
                check(value.seconds() == seconds && value.nanoseconds() == 999_999_999);
            }
        }
        for (long seconds : new long[]{-9_223_372_037L,9_223_372_036L}) {
            try (ReadOnlyFileSession outside = session(root)) {
                // These microsecond-aligned values survive FileTime round-trip,
                // reproducing the old check's inability to detect JDK truncation.
                FileTime time = FileTime.from(Instant.ofEpochSecond(seconds,123_456_000));
                check(FileTime.from(time.toInstant()).equals(time));
                terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, () -> outside.timestamp(time));
                check(outside.stats().operations() == 0 && outside.stats().opened() == 0);
            }
        }
    }
    private static void metadataAndBytes(Path root) throws Exception {
        Path file = root.resolve("data"); byte[] bytes = {65, 13, 10, 0, (byte) 0xff, 66, 10, 67}; Files.write(file, bytes);
        Files.createLink(root.resolve("hard"), file);
        Files.setLastModifiedTime(file, FileTime.from(Instant.ofEpochSecond(-3, 123456789)));
        try (ReadOnlyFileSession files = session(root)) {
            ReadOnlyFileSession.Metadata metadata = files.metadata("data");
            Map<String, Object> actual = Files.readAttributes(file, "unix:lastAccessTime,lastModifiedTime,size,nlink,mode");
            Instant modified = ((FileTime) actual.get("lastModifiedTime")).toInstant();
            Instant accessed = ((FileTime) actual.get("lastAccessTime")).toInstant();
            check(metadata.size() == bytes.length && metadata.links() == ((Integer) actual.get("nlink")).longValue());
            check(metadata.mode() == (Integer) actual.get("mode") && metadata.kind() == ReadOnlyFileSession.FileKind.REGULAR);
            check(metadata.modified().seconds() == modified.getEpochSecond() && metadata.modified().nanoseconds() == modified.getNano());
            check(metadata.accessed().seconds() == accessed.getEpochSecond() && metadata.accessed().nanoseconds() == accessed.getNano());
            check(files.metadata(".").kind() == ReadOnlyFileSession.FileKind.DIRECTORY);
            ReadOnlyFileSession.Handle handle = files.open("data"); check(handle.id() > 0 && !handle.isClosed());
            check(Arrays.equals(files.read(handle, 0), new byte[0])); check(files.stats().bytesRead() == 0);
            long operations = files.stats().operations();
            files.write(handle, new byte[0]); files.putStr(handle, "");
            check(files.stats().operations() == operations + 2 && files.stats().bytesRead() == 0);
            check(Arrays.equals(Files.readAllBytes(file), bytes));
            check(Arrays.equals(files.getLine(handle), new byte[]{65, 13, 10}));
            check(Arrays.equals(files.read(handle, 2), new byte[]{0, (byte) 0xff}));
            files.flush(handle); // input fflush must not skip unread prefetch
            check(Arrays.equals(files.getLine(handle), new byte[]{66, 10}));
            check(Arrays.equals(files.getLine(handle), new byte[]{67}));
            check(files.getLine(handle).length == 0 && files.read(handle, 1).length == 0);
            Files.write(file, new byte[]{68}, StandardOpenOption.APPEND);
            check(Arrays.equals(files.read(handle, 1), new byte[]{68})); // no sticky EOF or file snapshot
            check(!files.isTty(handle));
            guest(9, ReadOnlyFileSession.Operation.WRITE, () -> files.write(handle, new byte[]{90}));
            guest(9, ReadOnlyFileSession.Operation.PUT_STR, () -> files.putStr(handle, "overwrite"));
            check(Files.readAllBytes(file)[0] == 65);
            handle.close(); handle.close(); check(files.stats().closeAttempts() == 1 && files.stats().liveHandles() == 0);
            terminal(ReadOnlyFileSession.Code.INVALID_HANDLE, () -> files.write(handle, new byte[0]));
            terminal(ReadOnlyFileSession.Code.INVALID_HANDLE, () -> files.putStr(handle, ""));
            terminal(ReadOnlyFileSession.Code.INVALID_HANDLE, () -> files.read(handle, 0));
        }
    }
    private static void pathsAndLimits(Path root) throws Exception {
        try (ReadOnlyFileSession files = session(root)) {
            guest(2, ReadOnlyFileSession.Operation.METADATA, () -> files.metadata("missing"));
            guest(2, ReadOnlyFileSession.Operation.OPEN, () -> files.open(""));
            guest(22, ReadOnlyFileSession.Operation.OPEN, () -> files.open("bad\0path"));
            guest(20, ReadOnlyFileSession.Operation.OPEN, () -> files.open("data/child"));
            check(files.stats().opened() == 0);
        }
        Files.createSymbolicLink(root.resolve("link"), Path.of("data"));
        for (String path : new String[]{"../escape", root.resolve("data").toString(), "link"}) {
            try (ReadOnlyFileSession files = session(root)) { terminal(ReadOnlyFileSession.Code.POLICY, () -> files.open(path)); }
        }
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(1, 4, 8, 100))) {
            ReadOnlyFileSession.Handle first = files.open("data");
            terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.open("data"));
            first.close(); check(files.stats().liveHandles() == 0);
        }
        for (long count : new long[]{5, -1}) {
            try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(1, 4, 8, 100))) {
                ReadOnlyFileSession.Handle h = files.open("data");
                terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.read(h, count)); check(files.stats().bytesRead() == 0);
            }
        }
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(1, 4, 3, 100))) {
            ReadOnlyFileSession.Handle h = files.open("data"); files.read(h, 3);
            terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.read(h, 1)); check(files.stats().bytesRead() == 3);
        }
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(1, 4, 16, 1))) {
            files.open("data"); terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.metadata("data"));
        }
        Files.write(root.resolve("long-line"), new byte[5]);
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(1, 4, 16, 10))) {
            ReadOnlyFileSession.Handle h = files.open("long-line");
            terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.getLine(h));
        }
        Files.write(root.resolve("exact-line"), new byte[]{65, 66, 67, 68}); Files.write(root.resolve("empty"), new byte[0]);
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(2, 4, 16, 10))) {
            ReadOnlyFileSession.Handle exact = files.open("exact-line"), empty = files.open("empty");
            check(Arrays.equals(files.getLine(exact), new byte[]{65, 66, 67, 68}));
            check(files.getLine(empty).length == 0 && files.read(empty, 1).length == 0);
        }
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."),
                new ReadOnlyFileSession.Limits(1, 4, 16, 10, 4))) {
            terminal(ReadOnlyFileSession.Code.RESOURCE_LIMIT, () -> files.open("large\0path"));
        }
        ReadOnlyFileSession a = session(root), b = session(root); ReadOnlyFileSession.Handle h = a.open("data");
        terminal(ReadOnlyFileSession.Code.INVALID_HANDLE, () -> b.isTty(h));
        a.close(); b.close(); a.close(); check(h.isClosed() && a.stats().closeAttempts() == 1);
        terminal(ReadOnlyFileSession.Code.CLOSED, () -> a.metadata("data"));
    }
    private static void failuresAndRetirement(Path root) throws Exception {
        List<CountedChannel> channels = new ArrayList<>();
        ReadOnlyFileSession.Opener opener = path -> { CountedChannel c = new CountedChannel(path); channels.add(c); return c; };
        ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(4, 32, 100, 100), opener);
        ReadOnlyFileSession.Handle h1 = files.open("data"), h2 = files.open("data");
        channels.get(0).closeFailure = new IOException("close failed");
        h1.close(); h1.close();
        terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, files::close);
        terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, files::close); h2.close();
        check(channels.get(0).closes == 1 && channels.get(1).closes == 1 && files.stats().liveHandles() == 1);
        check(!channels.get(0).delegate.isOpen()); // even this known test fact is not an engine certificate
        check(files.stats().closeDiagnostics().size() == 1);
        try (ReadOnlyFileSession denied = new ReadOnlyFileSession(root, Path.of("."), limits(1, 32, 100, 100),
                path -> { throw new AccessDeniedException(path.toString()); })) {
            guest(13, ReadOnlyFileSession.Operation.OPEN, () -> denied.open("data")); check(denied.stats().liveHandles() == 0);
        }
        for (boolean interrupted : new boolean[]{false, true}) {
            channels.clear();
            try (ReadOnlyFileSession failed = new ReadOnlyFileSession(root, Path.of("."), limits(1, 32, 100, 100), opener)) {
                ReadOnlyFileSession.Handle h = failed.open("data");
                channels.get(0).readFailure = interrupted ? new InterruptedIOException("interrupted") : new IOException("unknown");
                ReadOnlyFileSession.Terminal first = terminal(interrupted ? ReadOnlyFileSession.Code.CANCELLED
                        : ReadOnlyFileSession.Code.PROVIDER_FAILURE, () -> failed.read(h, 1));
                check(first == terminal(first.code(), () -> failed.read(h, 1)));
                check(Thread.currentThread().isInterrupted() == interrupted); Thread.interrupted();
            }
            check(channels.get(0).closes == 1);
        }
        channels.clear();
        try (ReadOnlyFileSession failed = new ReadOnlyFileSession(root, Path.of("."), limits(1, 32, 100, 100), opener)) {
            ReadOnlyFileSession.Handle h = failed.open("data"); Error original = new AssertionError("read fatal");
            channels.get(0).readError = original;
            try { failed.read(h, 1); throw new AssertionError("Fatal error swallowed"); }
            catch (Error failure) { check(failure == original); }
        }
        check(channels.get(0).closes == 1);
        channels.clear();
        ReadOnlyFileSession fatal = new ReadOnlyFileSession(root, Path.of("."), limits(4, 32, 100, 100), opener);
        fatal.open("data"); fatal.open("data"); Error original = new AssertionError("close fatal"); channels.get(0).closeError = original;
        try { fatal.close(); throw new AssertionError("Fatal close swallowed"); } catch (Error failure) { check(failure == original); }
        check(channels.get(0).closes == 1 && channels.get(1).closes == 1 && fatal.stats().liveHandles() == 1);
        terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, fatal::close); check(channels.get(0).closes == 1);
    }
    private static void uncertainCloseCustody(Path root) throws Exception {
        for (boolean error : new boolean[]{false,true}) {
            List<CountedChannel> channels = new ArrayList<>();
            ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(4,32,100,100), path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
            });
            ReadOnlyFileSession.Handle first = files.open("data"); files.open("data");
            CountedChannel uncertain = channels.get(0); uncertain.closeFailureBeforeDelegate = true;
            Error original = new AssertionError("before real descriptor close");
            if (error) uncertain.closeError = original; else uncertain.closeFailure = new IOException("before delegate");
            try {
                if (error) {
                    try { files.close(); throw new AssertionError("Fatal close swallowed"); }
                    catch (Error actual) { check(actual == original); }
                } else terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, files::close);
                // The abstract channel is closed even though the real delegate
                // remains open: isOpen must never authorize ledger removal.
                check(!uncertain.isOpen() && uncertain.delegate.isOpen());
                check(files.stats().closed() && files.stats().liveHandles() == 1);
                check(uncertain.closes == 1 && channels.get(1).closes == 1);
                check(!channels.get(1).delegate.isOpen());
                first.close(); terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, files::close);
                check(uncertain.closes == 1 && files.stats().closeAttempts() == 2);
            } finally {
                // Explicit test custody cleanup, not a claimed engine retirement.
                for (CountedChannel channel : channels) channel.delegate.close();
            }
        }
        List<CountedChannel> channels = new ArrayList<>();
        ReadOnlyFileSession files = new ReadOnlyFileSession(root, Path.of("."), limits(4,32,100,100), path -> {
            CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
        });
        files.open("data"); files.open("data"); files.open("data");
        channels.get(0).closeFailureBeforeDelegate = true; channels.get(0).closeError = new AssertionError("first fatal");
        channels.get(1).closeFailureBeforeDelegate = true;
        Error vm = new OutOfMemoryError("synthetic before-delegate fatal"); channels.get(1).closeError = vm;
        try {
            try { files.close(); throw new AssertionError("VM error swallowed"); }
            catch (Error actual) { check(actual == vm); }
            check(files.stats().liveHandles() == 2 && files.stats().closeAttempts() == 3);
            check(channels.get(2).closes == 1 && !channels.get(2).delegate.isOpen());
            terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, files::close);
            check(channels.get(0).closes == 1 && channels.get(1).closes == 1);
        } finally { for (CountedChannel channel : channels) channel.delegate.close(); }
    }
    private static void stickyFileErrors(Path root) throws Exception {
        byte[] contents = {65,10,66}; Files.write(root.resolve("sticky-error"),contents);
        for (boolean stringWrite : new boolean[]{false,true}) {
            for (int preserve : new int[]{0,1,2}) {
                try (ReadOnlyFileSession files = session(root)) {
                    ReadOnlyFileSession.Handle h = files.open("sticky-error");
                    if (stringWrite) guest(9,ReadOnlyFileSession.Operation.PUT_STR,() -> files.putStr(h,"x"));
                    else guest(9,ReadOnlyFileSession.Operation.WRITE,() -> files.write(h,new byte[]{88}));
                    if (preserve == 0) {
                        files.write(h,new byte[0]); files.putStr(h,"");
                        check(files.read(h,0).length == 0); // neither empty IO clears ferror
                    } else if (preserve == 1) {
                        // A short positive read also sees EOF internally, but
                        // native Handle.read returns before clearerr in this case.
                        check(Arrays.equals(files.read(h,32),contents));
                    } else files.flush(h); // fflush does not clear the FILE error
                    long before = files.stats().bytesRead();
                    terminal(ReadOnlyFileSession.Code.POLICY,() -> files.getLine(h));
                    check(files.stats().bytesRead() == before); // refusal precedes line consumption
                }
            }
            try (ReadOnlyFileSession files = session(root)) {
                ReadOnlyFileSession.Handle h = files.open("sticky-error");
                if (stringWrite) guest(9,ReadOnlyFileSession.Operation.PUT_STR,() -> files.putStr(h,"x"));
                else guest(9,ReadOnlyFileSession.Operation.WRITE,() -> files.write(h,new byte[]{88}));
                check(Arrays.equals(files.read(h,32),contents));
                check(files.read(h,1).length == 0); // empty EOF executes clearerr
                check(files.getLine(h).length == 0);
            }
        }
        List<CountedChannel> channels = new ArrayList<>();
        try (ReadOnlyFileSession files = new ReadOnlyFileSession(root,Path.of("."),limits(1,32,100,100),path -> {
            CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
        })) {
            ReadOnlyFileSession.Handle h = files.open("sticky-error");
            channels.get(0).readFailure = new AccessDeniedException("synthetic read failure");
            guest(13,ReadOnlyFileSession.Operation.READ,() -> files.read(h,1));
            channels.get(0).readFailure = null;
            terminal(ReadOnlyFileSession.Code.POLICY,() -> files.getLine(h));
            check(files.stats().bytesRead() == 0);
        }
    }
    private static void acquisitionCleanupFatalPriority(Path root) throws Exception {
        for (Error fatal : new Error[]{new OutOfMemoryError("synthetic acquisition cleanup"),new ThreadDeath()}) {
            List<CountedChannel> channels = new ArrayList<>();
            ReadOnlyFileSession files = new ReadOnlyFileSession(root,Path.of("."),limits(1,32,100,100),path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel);
                channel.closeFailureBeforeDelegate = true; channel.closeError = fatal;
                Thread.currentThread().interrupt(); return channel;
            });
            try {
                try { files.open("data"); throw new AssertionError("VM cleanup fatal swallowed"); }
                catch (Error actual) { check(actual == fatal); }
                check(Thread.currentThread().isInterrupted()); Thread.interrupted();
                check(files.stats().opened() == 1 && files.stats().liveHandles() == 1);
                check(channels.get(0).closes == 1 && channels.get(0).delegate.isOpen());
                terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE,files::close);
                check(channels.get(0).closes == 1); // uncertain cleanup never replays
            } finally {
                Thread.interrupted();
                for (CountedChannel channel : channels) channel.delegate.close();
            }
        }
    }
    private static void cancellation(Path root) throws Exception {
        boolean previous = Thread.interrupted();
        try {
            try (ReadOnlyFileSession before = session(root)) {
                Thread.currentThread().interrupt(); terminal(ReadOnlyFileSession.Code.CANCELLED, () -> before.open("data"));
                check(before.stats().opened() == 0 && Thread.currentThread().isInterrupted()); Thread.interrupted();
            }
            List<CountedChannel> channels = new ArrayList<>();
            Error cleanupFatal = new AssertionError("secondary cleanup failure");
            ReadOnlyFileSession.Opener opener = path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel);
                channel.closeError = cleanupFatal;
                Thread.currentThread().interrupt(); return channel;
            };
            ReadOnlyFileSession afterOpen = new ReadOnlyFileSession(root, Path.of("."), limits(1, 32, 100, 100), opener);
            try { afterOpen.open("data"); throw new AssertionError("Fatal cleanup swallowed"); }
            catch (Error actual) { check(actual == cleanupFatal); }
            check(afterOpen.stats().opened() == 1 && afterOpen.stats().liveHandles() == 1 && channels.get(0).closes == 1);
            check(Thread.currentThread().isInterrupted()); Thread.interrupted();
            terminal(ReadOnlyFileSession.Code.PROVIDER_FAILURE, afterOpen::close);
            check(channels.get(0).closes == 1 && !channels.get(0).delegate.isOpen());
            channels.clear();
            try (ReadOnlyFileSession after = new ReadOnlyFileSession(root, Path.of("."), limits(1, 32, 100, 100), path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
            })) {
                ReadOnlyFileSession.Handle h = after.open("data"); channels.get(0).interruptAfterRead = true;
                terminal(ReadOnlyFileSession.Code.CANCELLED, () -> after.read(h, 2));
                check(after.stats().bytesRead() == 2 && after.stats().liveHandles() == 1);
                check(Thread.currentThread().isInterrupted()); Thread.interrupted();
            }
            check(channels.get(0).closes == 1);
        } finally { Thread.interrupted(); if (previous) Thread.currentThread().interrupt(); }
    }
    public static void main(String[] arguments) throws Exception {
        if (arguments.length != 1) throw new IllegalArgumentException("Pass a new test-root path");
        Path root = Path.of(arguments[0]).toAbsolutePath(); Files.createDirectory(root);
        try {
            metadataAndBytes(root); ownerAndTimestampDomains(root); pathsAndLimits(root); failuresAndRetirement(root); uncertainCloseCustody(root); stickyFileErrors(root); acquisitionCleanupFatalPriority(root); cancellation(root);
            System.out.println("READ_ONLY_FILE_SESSION_CHECKS " + checks);
        } finally {
            try (var paths = Files.walk(root)) {
                for (Path path : paths.sorted(java.util.Comparator.reverseOrder()).toList()) Files.deleteIfExists(path);
            }
        }
    }
}
