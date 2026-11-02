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
public final class FileSessionChecks {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    @FunctionalInterface interface Action { void run() throws Exception; }
    private static FileSession.Terminal terminal(FileSession.Code code, Action action) throws Exception {
        try { action.run(); throw new AssertionError("Expected terminal " + code); }
        catch (FileSession.Terminal failure) { check(failure.code() == code); return failure; }
    }
    private static void guest(int errno, FileSession.Operation operation, Action action) throws Exception {
        try { action.run(); throw new AssertionError("Expected guest failure"); }
        catch (FileSession.FSFailure failure) { check(failure.errno() == errno); check(failure.operation() == operation); }
    }
    private static FileSession.Limits limits(int handles, int read, long total, long operations) {
        return new FileSession.Limits(handles, read, total, operations, 4096);
    }
    private static FileSession session(Path root) throws Exception {
        return new FileSession(root, Path.of("."), limits(4, 65536, 1048576, 1000));
    }
    private static final class CountedChannel extends FileChannel {
        final FileChannel delegate;
        int closes;
        boolean interruptAfterRead, interruptAfterWrite, closeFailureBeforeDelegate, zeroWrite, failAfterWrite;
        boolean failRestoration, truncated;
        int maxWrite = Integer.MAX_VALUE;
        IOException readFailure, closeFailure, writeFailure;
        Error readError, closeError;
        CountedChannel(Path path) throws IOException { this(path, false); }
        CountedChannel(Path path, boolean writable) throws IOException { this(path, writable, false); }
        CountedChannel(Path path, boolean writable, boolean append) throws IOException {
            delegate = append ? FileChannel.open(path, StandardOpenOption.WRITE, StandardOpenOption.APPEND)
                    : writable ? FileChannel.open(path, StandardOpenOption.READ, StandardOpenOption.WRITE)
                    : FileChannel.open(path, StandardOpenOption.READ);
        }
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
        @Override public FileChannel position(long offset) throws IOException {
            if (failRestoration && truncated) throw new IOException("controlled position restoration failure");
            delegate.position(offset); return this;
        }
        @Override public long size() throws IOException { return delegate.size(); }
        @Override public long read(ByteBuffer[] b, int o, int n) throws IOException { return delegate.read(b, o, n); }
        @Override public int read(ByteBuffer b, long p) throws IOException { return delegate.read(b, p); }
        @Override public int write(ByteBuffer b) throws IOException {
            if (zeroWrite) return 0;
            int end = b.limit(); b.limit(Math.min(end, b.position() + maxWrite));
            int n;
            try { n = delegate.write(b); } finally { b.limit(end); }
            if (interruptAfterWrite) Thread.currentThread().interrupt();
            if (writeFailure != null) throw writeFailure;
            if (failAfterWrite) throw new IOException("unknown controlled failure after partial acceptance");
            return n;
        }
        @Override public long write(ByteBuffer[] b, int o, int n) throws IOException { return delegate.write(b, o, n); }
        @Override public int write(ByteBuffer b, long p) throws IOException { return delegate.write(b, p); }
        @Override public FileChannel truncate(long n) throws IOException { delegate.truncate(n); truncated = true; return this; }
        @Override public void force(boolean m) throws IOException { delegate.force(m); }
        @Override public long transferTo(long p, long n, WritableByteChannel c) throws IOException { return delegate.transferTo(p, n, c); }
        @Override public long transferFrom(ReadableByteChannel c, long p, long n) throws IOException { return delegate.transferFrom(c, p, n); }
        @Override public MappedByteBuffer map(MapMode m, long p, long n) throws IOException { return delegate.map(m, p, n); }
        @Override public FileLock lock(long p, long n, boolean shared) throws IOException { return delegate.lock(p, n, shared); }
        @Override public FileLock tryLock(long p, long n, boolean shared) throws IOException { return delegate.tryLock(p, n, shared); }
    }
    private static void claimRefused(FileSession files, Object owner) {
        FileSession.Stats before = files.stats();
        try { files.claimOwner(owner); throw new AssertionError("Session claim accepted"); }
        catch (IllegalArgumentException | IllegalStateException expected) { checks++; }
        check(before.equals(files.stats()));
    }
    private static void ownerAndTimestampDomains(Path root) throws Exception {
        Object owner = new Object();
        try (FileSession fresh = session(root)) {
            claimRefused(fresh, null); claimRefused(fresh, "not an inert identity");
            check(fresh.stats().operations() == 0 && fresh.stats().opened() == 0);
            fresh.claimOwner(owner);
            claimRefused(fresh, owner); claimRefused(fresh, new Object());
            // Rejected second claims do not poison the already bound session.
            check(fresh.metadata(".").kind() == FileSession.FileKind.DIRECTORY);
        }
        try (FileSession used = session(root)) {
            used.metadata("."); claimRefused(used, new Object());
        }
        try (FileSession used = session(root)) {
            FileSession.Handle handle = used.open("data"); handle.close();
            check(used.stats().liveHandles() == 0); claimRefused(used, new Object());
        }
        FileSession closed = session(root); closed.close(); claimRefused(closed, new Object());
        try (FileSession failed = session(root)) {
            terminal(FileSession.Code.PROVIDER_FAILURE, () -> failed.timestamp("not a FileTime"));
            claimRefused(failed, new Object());
        }
        try (FileSession exact = session(root)) {
            for (long seconds : new long[]{-9_223_372_036L,-3,0,9_223_372_035L}) {
                FileTime time = FileTime.from(Instant.ofEpochSecond(seconds,999_999_999));
                FileSession.Timestamp value = exact.timestamp(time);
                check(value.seconds() == seconds && value.nanoseconds() == 999_999_999);
            }
        }
        for (long seconds : new long[]{-9_223_372_037L,9_223_372_036L}) {
            try (FileSession outside = session(root)) {
                // These microsecond-aligned values survive FileTime round-trip,
                // reproducing the old check's inability to detect JDK truncation.
                FileTime time = FileTime.from(Instant.ofEpochSecond(seconds,123_456_000));
                check(FileTime.from(time.toInstant()).equals(time));
                terminal(FileSession.Code.PROVIDER_FAILURE, () -> outside.timestamp(time));
                check(outside.stats().operations() == 0 && outside.stats().opened() == 0);
            }
        }
    }
    private static void metadataAndBytes(Path root) throws Exception {
        Path file = root.resolve("data"); byte[] bytes = {65, 13, 10, 0, (byte) 0xff, 66, 10, 67}; Files.write(file, bytes);
        Files.createLink(root.resolve("hard"), file);
        Files.setLastModifiedTime(file, FileTime.from(Instant.ofEpochSecond(-3, 123456789)));
        try (FileSession files = session(root)) {
            FileSession.Metadata metadata = files.metadata("data");
            Map<String, Object> actual = Files.readAttributes(file, "unix:lastAccessTime,lastModifiedTime,size,nlink,mode");
            Instant modified = ((FileTime) actual.get("lastModifiedTime")).toInstant();
            Instant accessed = ((FileTime) actual.get("lastAccessTime")).toInstant();
            check(metadata.size() == bytes.length && metadata.links() == ((Integer) actual.get("nlink")).longValue());
            check(metadata.mode() == (Integer) actual.get("mode") && metadata.kind() == FileSession.FileKind.REGULAR);
            check(metadata.modified().seconds() == modified.getEpochSecond() && metadata.modified().nanoseconds() == modified.getNano());
            check(metadata.accessed().seconds() == accessed.getEpochSecond() && metadata.accessed().nanoseconds() == accessed.getNano());
            check(files.metadata(".").kind() == FileSession.FileKind.DIRECTORY);
            FileSession.Handle handle = files.open("data"); check(handle.id() > 0 && !handle.isClosed());
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
            guest(9, FileSession.Operation.WRITE, () -> files.write(handle, new byte[]{90}));
            guest(9, FileSession.Operation.PUT_STR, () -> files.putStr(handle, "overwrite"));
            check(Files.readAllBytes(file)[0] == 65);
            handle.close(); handle.close(); check(files.stats().closeAttempts() == 1 && files.stats().liveHandles() == 0);
            terminal(FileSession.Code.INVALID_HANDLE, () -> files.write(handle, new byte[0]));
            terminal(FileSession.Code.INVALID_HANDLE, () -> files.putStr(handle, ""));
            terminal(FileSession.Code.INVALID_HANDLE, () -> files.read(handle, 0));
        }
    }
    private static void pathsAndLimits(Path root) throws Exception {
        try (FileSession files = session(root)) {
            guest(2, FileSession.Operation.METADATA, () -> files.metadata("missing"));
            guest(2, FileSession.Operation.OPEN, () -> files.open(""));
            guest(22, FileSession.Operation.OPEN, () -> files.open("bad\0path"));
            guest(20, FileSession.Operation.OPEN, () -> files.open("data/child"));
            check(files.stats().opened() == 0);
        }
        Files.createSymbolicLink(root.resolve("link"), Path.of("data"));
        for (String path : new String[]{"../escape", root.resolve("data").toString(), "link"}) {
            try (FileSession files = session(root)) { terminal(FileSession.Code.POLICY, () -> files.open(path)); }
        }
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 4, 8, 100))) {
            FileSession.Handle first = files.open("data");
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.open("data"));
            first.close(); check(files.stats().liveHandles() == 0);
        }
        for (long count : new long[]{5, -1}) {
            try (FileSession files = new FileSession(root, Path.of("."), limits(1, 4, 8, 100))) {
                FileSession.Handle h = files.open("data");
                terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.read(h, count)); check(files.stats().bytesRead() == 0);
            }
        }
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 4, 3, 100))) {
            FileSession.Handle h = files.open("data"); files.read(h, 3);
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.read(h, 1)); check(files.stats().bytesRead() == 3);
        }
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 4, 16, 1))) {
            files.open("data"); terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.metadata("data"));
        }
        Files.write(root.resolve("long-line"), new byte[5]);
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 4, 16, 10))) {
            FileSession.Handle h = files.open("long-line");
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.getLine(h));
        }
        Files.write(root.resolve("exact-line"), new byte[]{65, 66, 67, 68}); Files.write(root.resolve("empty"), new byte[0]);
        try (FileSession files = new FileSession(root, Path.of("."), limits(2, 4, 16, 10))) {
            FileSession.Handle exact = files.open("exact-line"), empty = files.open("empty");
            check(Arrays.equals(files.getLine(exact), new byte[]{65, 66, 67, 68}));
            check(files.getLine(empty).length == 0 && files.read(empty, 1).length == 0);
        }
        try (FileSession files = new FileSession(root, Path.of("."),
                new FileSession.Limits(1, 4, 16, 10, 4))) {
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.open("large\0path"));
        }
        FileSession a = session(root), b = session(root); FileSession.Handle h = a.open("data");
        terminal(FileSession.Code.INVALID_HANDLE, () -> b.isTty(h));
        a.close(); b.close(); a.close(); check(h.isClosed() && a.stats().closeAttempts() == 1);
        terminal(FileSession.Code.CLOSED, () -> a.metadata("data"));
    }
    private static void failuresAndRetirement(Path root) throws Exception {
        List<CountedChannel> channels = new ArrayList<>();
        FileSession.Opener opener = path -> { CountedChannel c = new CountedChannel(path); channels.add(c); return c; };
        FileSession files = new FileSession(root, Path.of("."), limits(4, 32, 100, 100), opener);
        FileSession.Handle h1 = files.open("data"), h2 = files.open("data");
        channels.get(0).closeFailure = new IOException("close failed");
        h1.close(); h1.close();
        terminal(FileSession.Code.PROVIDER_FAILURE, files::close);
        terminal(FileSession.Code.PROVIDER_FAILURE, files::close); h2.close();
        check(channels.get(0).closes == 1 && channels.get(1).closes == 1 && files.stats().liveHandles() == 1);
        check(!channels.get(0).delegate.isOpen()); // even this known test fact is not an engine certificate
        check(files.stats().closeDiagnostics().size() == 1);
        try (FileSession denied = new FileSession(root, Path.of("."), limits(1, 32, 100, 100),
                path -> { throw new AccessDeniedException(path.toString()); })) {
            guest(13, FileSession.Operation.OPEN, () -> denied.open("data")); check(denied.stats().liveHandles() == 0);
        }
        for (boolean interrupted : new boolean[]{false, true}) {
            channels.clear();
            try (FileSession failed = new FileSession(root, Path.of("."), limits(1, 32, 100, 100), opener)) {
                FileSession.Handle h = failed.open("data");
                channels.get(0).readFailure = interrupted ? new InterruptedIOException("interrupted") : new IOException("unknown");
                FileSession.Terminal first = terminal(interrupted ? FileSession.Code.CANCELLED
                        : FileSession.Code.PROVIDER_FAILURE, () -> failed.read(h, 1));
                check(first == terminal(first.code(), () -> failed.read(h, 1)));
                check(Thread.currentThread().isInterrupted() == interrupted); Thread.interrupted();
            }
            check(channels.get(0).closes == 1);
        }
        channels.clear();
        try (FileSession failed = new FileSession(root, Path.of("."), limits(1, 32, 100, 100), opener)) {
            FileSession.Handle h = failed.open("data"); Error original = new AssertionError("read fatal");
            channels.get(0).readError = original;
            try { failed.read(h, 1); throw new AssertionError("Fatal error swallowed"); }
            catch (Error failure) { check(failure == original); }
        }
        check(channels.get(0).closes == 1);
        channels.clear();
        FileSession fatal = new FileSession(root, Path.of("."), limits(4, 32, 100, 100), opener);
        fatal.open("data"); fatal.open("data"); Error original = new AssertionError("close fatal"); channels.get(0).closeError = original;
        try { fatal.close(); throw new AssertionError("Fatal close swallowed"); } catch (Error failure) { check(failure == original); }
        check(channels.get(0).closes == 1 && channels.get(1).closes == 1 && fatal.stats().liveHandles() == 1);
        terminal(FileSession.Code.PROVIDER_FAILURE, fatal::close); check(channels.get(0).closes == 1);
    }
    private static void uncertainCloseCustody(Path root) throws Exception {
        for (boolean error : new boolean[]{false,true}) {
            List<CountedChannel> channels = new ArrayList<>();
            FileSession files = new FileSession(root, Path.of("."), limits(4,32,100,100), path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
            });
            FileSession.Handle first = files.open("data"); files.open("data");
            CountedChannel uncertain = channels.get(0); uncertain.closeFailureBeforeDelegate = true;
            Error original = new AssertionError("before real descriptor close");
            if (error) uncertain.closeError = original; else uncertain.closeFailure = new IOException("before delegate");
            try {
                if (error) {
                    try { files.close(); throw new AssertionError("Fatal close swallowed"); }
                    catch (Error actual) { check(actual == original); }
                } else terminal(FileSession.Code.PROVIDER_FAILURE, files::close);
                // The abstract channel is closed even though the real delegate
                // remains open: isOpen must never authorize ledger removal.
                check(!uncertain.isOpen() && uncertain.delegate.isOpen());
                check(files.stats().closed() && files.stats().liveHandles() == 1);
                check(uncertain.closes == 1 && channels.get(1).closes == 1);
                check(!channels.get(1).delegate.isOpen());
                first.close(); terminal(FileSession.Code.PROVIDER_FAILURE, files::close);
                check(uncertain.closes == 1 && files.stats().closeAttempts() == 2);
            } finally {
                // Explicit test custody cleanup, not a claimed engine retirement.
                for (CountedChannel channel : channels) channel.delegate.close();
            }
        }
        List<CountedChannel> channels = new ArrayList<>();
        FileSession files = new FileSession(root, Path.of("."), limits(4,32,100,100), path -> {
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
            terminal(FileSession.Code.PROVIDER_FAILURE, files::close);
            check(channels.get(0).closes == 1 && channels.get(1).closes == 1);
        } finally { for (CountedChannel channel : channels) channel.delegate.close(); }
    }
    private static void stickyFileErrors(Path root) throws Exception {
        byte[] contents = {65,10,66}; Files.write(root.resolve("sticky-error"),contents);
        for (boolean stringWrite : new boolean[]{false,true}) {
            for (int preserve : new int[]{0,1,2}) {
                try (FileSession files = session(root)) {
                    FileSession.Handle h = files.open("sticky-error");
                    if (stringWrite) guest(9,FileSession.Operation.PUT_STR,() -> files.putStr(h,"x"));
                    else guest(9,FileSession.Operation.WRITE,() -> files.write(h,new byte[]{88}));
                    if (preserve == 0) {
                        files.write(h,new byte[0]); files.putStr(h,"");
                        check(files.read(h,0).length == 0); // neither empty IO clears ferror
                    } else if (preserve == 1) {
                        // A short positive read also sees EOF internally, but
                        // native Handle.read returns before clearerr in this case.
                        check(Arrays.equals(files.read(h,32),contents));
                    } else files.flush(h); // fflush does not clear the FILE error
                    long before = files.stats().bytesRead();
                    terminal(FileSession.Code.POLICY,() -> files.getLine(h));
                    check(files.stats().bytesRead() == before); // refusal precedes line consumption
                }
            }
            try (FileSession files = session(root)) {
                FileSession.Handle h = files.open("sticky-error");
                if (stringWrite) guest(9,FileSession.Operation.PUT_STR,() -> files.putStr(h,"x"));
                else guest(9,FileSession.Operation.WRITE,() -> files.write(h,new byte[]{88}));
                check(Arrays.equals(files.read(h,32),contents));
                check(files.read(h,1).length == 0); // empty EOF executes clearerr
                check(files.getLine(h).length == 0);
            }
        }
        List<CountedChannel> channels = new ArrayList<>();
        try (FileSession files = new FileSession(root,Path.of("."),limits(1,32,100,100),path -> {
            CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
        })) {
            FileSession.Handle h = files.open("sticky-error");
            channels.get(0).readFailure = new AccessDeniedException("synthetic read failure");
            guest(13,FileSession.Operation.READ,() -> files.read(h,1));
            channels.get(0).readFailure = null;
            terminal(FileSession.Code.POLICY,() -> files.getLine(h));
            check(files.stats().bytesRead() == 0);
        }
    }
    private static void acquisitionCleanupFatalPriority(Path root) throws Exception {
        for (Error fatal : new Error[]{new OutOfMemoryError("synthetic acquisition cleanup"),new ThreadDeath()}) {
            List<CountedChannel> channels = new ArrayList<>();
            FileSession files = new FileSession(root,Path.of("."),limits(1,32,100,100),path -> {
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
                terminal(FileSession.Code.PROVIDER_FAILURE,files::close);
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
            try (FileSession before = session(root)) {
                Thread.currentThread().interrupt(); terminal(FileSession.Code.CANCELLED, () -> before.open("data"));
                check(before.stats().opened() == 0 && Thread.currentThread().isInterrupted()); Thread.interrupted();
            }
            List<CountedChannel> channels = new ArrayList<>();
            Error cleanupFatal = new AssertionError("secondary cleanup failure");
            FileSession.Opener opener = path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel);
                channel.closeError = cleanupFatal;
                Thread.currentThread().interrupt(); return channel;
            };
            FileSession afterOpen = new FileSession(root, Path.of("."), limits(1, 32, 100, 100), opener);
            try { afterOpen.open("data"); throw new AssertionError("Fatal cleanup swallowed"); }
            catch (Error actual) { check(actual == cleanupFatal); }
            check(afterOpen.stats().opened() == 1 && afterOpen.stats().liveHandles() == 1 && channels.get(0).closes == 1);
            check(Thread.currentThread().isInterrupted()); Thread.interrupted();
            terminal(FileSession.Code.PROVIDER_FAILURE, afterOpen::close);
            check(channels.get(0).closes == 1 && !channels.get(0).delegate.isOpen());
            channels.clear();
            try (FileSession after = new FileSession(root, Path.of("."), limits(1, 32, 100, 100), path -> {
                CountedChannel channel = new CountedChannel(path); channels.add(channel); return channel;
            })) {
                FileSession.Handle h = after.open("data"); channels.get(0).interruptAfterRead = true;
                terminal(FileSession.Code.CANCELLED, () -> after.read(h, 2));
                check(after.stats().bytesRead() == 2 && after.stats().liveHandles() == 1);
                check(Thread.currentThread().isInterrupted()); Thread.interrupted();
            }
            check(channels.get(0).closes == 1);
        } finally { Thread.interrupted(); if (previous) Thread.currentThread().interrupt(); }
    }
    private static FileSession writable(Path root) throws Exception {
        return new FileSession(root, Path.of("."), limits(4, 65536, 1048576, 1000), true);
    }
    private static byte[] utf8(String s) { return s.getBytes(java.nio.charset.StandardCharsets.UTF_8); }
    private static void writingModes(Path root) throws Exception {
        Files.writeString(root.resolve("update"), "abc\ndef");
        try (FileSession files = writable(root)) {
            FileSession.Handle out = files.open("new", 2);
            files.write(out, new byte[0]); files.putStr(out, "é\0雪"); files.flush(out);
            check(Arrays.equals(Files.readAllBytes(root.resolve("new")), utf8("é\0雪")));
            files.rewind(out); files.write(out, new byte[]{65}); files.flush(out);
            check(Files.readAllBytes(root.resolve("new"))[0] == 65);
            guest(17, FileSession.Operation.OPEN, () -> files.open("new", 2));
            check(Files.readAllBytes(root.resolve("new")).length == 6);
            guest(2, FileSession.Operation.OPEN, () -> files.open("absent", 3));
            guest(2, FileSession.Operation.OPEN, () -> files.open("missing/leaf", 1));
            out.close();
            FileSession.Handle append = files.open("append", 4);
            files.putStr(append, "a"); files.rewind(append); files.putStr(append, "b"); files.flush(append);
            check(Files.readString(root.resolve("append")).equals("ab")); append.close();
            FileSession.Handle update = files.open("update", 3);
            check(Arrays.equals(files.getLine(update), utf8("abc\n")));
            files.rewind(update); files.putStr(update, "X"); files.flush(update);
            check(Arrays.equals(files.read(update, 3), utf8("bc\n")));
            files.rewind(update); files.putStr(update, "YZ"); files.flush(update); files.truncate(update);
            check(Files.readString(root.resolve("update")).equals("YZ"));
            files.rewind(update); check(Arrays.equals(files.read(update, 5), utf8("YZ")));
            files.write(update, new byte[]{0, (byte)255}); files.flush(update);
            check(Arrays.equals(Files.readAllBytes(root.resolve("update")), new byte[]{89,90,0,(byte)255}));
            update.close();
            FileSession.Handle truncate = files.open("new", 1);
            check(Files.size(root.resolve("new")) == 0); truncate.close();
            FileSession.Handle read = files.open("update", 0);
            guest(22, FileSession.Operation.TRUNCATE, () -> files.truncate(read));
            check(Arrays.equals(files.getLine(read), new byte[]{89,90,0,(byte)255}));
            check(files.stats().bytesWritten() == 14);
        }
        for (int mode = 1; mode <= 4; mode++) {
            final int selectedMode = mode;
            try (FileSession readonly = session(root)) {
                terminal(FileSession.Code.POLICY, () -> readonly.open("update", selectedMode));
                check(Files.size(root.resolve("update")) == 4 && readonly.stats().opened() == 0);
            }
            try (FileSession readonly = session(root)) {
                terminal(FileSession.Code.POLICY, () -> readonly.open("denied-new", selectedMode));
                check(!Files.exists(root.resolve("denied-new")) && readonly.stats().opened() == 0);
            }
        }
        try (FileSession files = writable(root)) {
            FileSession.Handle update = files.open("update", 3);
            files.read(update, 1); files.flush(update);
            terminal(FileSession.Code.POLICY, () -> files.write(update, new byte[]{88}));
            check(Files.readAllBytes(root.resolve("update"))[1] == 90);
        }
        try (FileSession files = writable(root)) {
            FileSession.Handle update = files.open("update", 3); files.putStr(update, "Q");
            terminal(FileSession.Code.POLICY, () -> files.read(update, 1));
        }
        try (FileSession files = writable(root)) {
            FileSession.Handle write = files.open("write-only", 1);
            check(files.read(write, 0).length == 0);
            guest(9, FileSession.Operation.READ, () -> files.read(write, 1));
            files.rewind(write);
            terminal(FileSession.Code.POLICY, () -> files.getLine(write));
        }
    }
    private static void writingBudgetsAndFailures(Path root) throws Exception {
        FileSession.Limits limits = new FileSession.Limits(2, 16, 0, 100, 4096, 4, 5);
        try (FileSession files = new FileSession(root, Path.of("."), limits, true)) {
            FileSession.Handle h = files.open("quota", 1); files.putStr(h, "éé"); files.write(h, new byte[]{1});
            check(files.stats().bytesRead() == 0 && files.stats().bytesWritten() == 5);
            files.rewind(h);
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.write(h, new byte[]{2}));
            check(Arrays.equals(Files.readAllBytes(root.resolve("quota")), new byte[]{(byte)195,(byte)169,(byte)195,(byte)169,1}));
        }
        try (FileSession files = new FileSession(root, Path.of("."), limits, true)) {
            FileSession.Handle h = files.open("too-big", 1);
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.putStr(h, "雪雪"));
            check(Files.size(root.resolve("too-big")) == 0 && files.stats().bytesWritten() == 0);
        }
        Files.writeString(root.resolve("partial"), "");
        for (int kind = 0; kind < 4; kind++) {
            final int variant = kind; List<CountedChannel> channels = new ArrayList<>();
            FileSession files = new FileSession(root, Path.of("."), limits(1, 10, 10, 100), true, path -> {
                CountedChannel channel = new CountedChannel(path, true); channel.maxWrite = 2;
                channel.zeroWrite = variant == 1; channel.failAfterWrite = variant == 2;
                channel.interruptAfterWrite = variant == 3; channels.add(channel); return channel;
            });
            try {
                FileSession.Handle h = files.open("partial", 3);
                if (kind == 0) { files.write(h, new byte[]{1,2,3,4,5}); check(files.stats().bytesWritten() == 5); }
                else {
                    terminal(kind == 3 ? FileSession.Code.CANCELLED : FileSession.Code.PROVIDER_FAILURE,
                            () -> files.write(h, new byte[]{1,2,3,4,5}));
                    check(files.stats().bytesWritten() == (kind == 1 ? 0 : 2));
                }
            } finally { Thread.interrupted(); files.close(); }
            check(channels.get(0).closes == 1 && files.stats().liveHandles() == 0);
        }
    }
    private static void appendLogicalCursor(Path root) throws Exception {
        Files.writeString(root.resolve("append-initial"), "seed");
        Files.writeString(root.resolve("append-rewind"), "seed");
        Files.writeString(root.resolve("append-rewind-flush"), "seed");
        Files.writeString(root.resolve("append-synced"), "seed");
        Files.writeString(root.resolve("append-after-rewind"), "seed");
        try (FileSession files = writable(root)) {
            FileSession.Handle initial = files.open("append-initial", 4);
            files.truncate(initial); check(Files.size(root.resolve("append-initial")) == 0); initial.close();
            FileSession.Handle positioned = files.open("append-rewind", 4);
            files.rewind(positioned); files.truncate(positioned);
            check(Files.size(root.resolve("append-rewind")) == 0); positioned.close();
            FileSession.Handle flushed = files.open("append-rewind-flush", 4);
            files.rewind(flushed); files.flush(flushed); files.truncate(flushed);
            check(Files.size(root.resolve("append-rewind-flush")) == 0); flushed.close();
            FileSession.Handle synced = files.open("append-synced", 4);
            files.putStr(synced, "X"); files.flush(synced); files.truncate(synced);
            check(Files.readString(root.resolve("append-synced")).equals("seedX")); synced.close();
            FileSession.Handle repeated = files.open("append-after-rewind", 4);
            files.putStr(repeated, "X"); files.rewind(repeated); files.putStr(repeated, "Y"); files.flush(repeated);
            files.truncate(repeated);
            check(Files.readString(root.resolve("append-after-rewind")).equals("seedXY")); repeated.close();
            check(files.stats().bytesWritten() == 3);
        }
        Files.writeString(root.resolve("append-partial"), "seed");
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 16, 16, 100), true, path -> {
            CountedChannel channel = new CountedChannel(path, true, true);
            channel.maxWrite = 2; channel.writeFailure = new IOException("No space left on device"); return channel;
        })) {
            FileSession.Handle h = files.open("append-partial", 4); files.rewind(h);
            guest(28, FileSession.Operation.WRITE, () -> files.write(h, utf8("XYZ")));
            files.flush(h); files.truncate(h);
            check(Files.readString(root.resolve("append-partial")).equals("seedXY"));
            check(files.stats().bytesWritten() == 2);
            files.rewind(h); files.flush(h); files.truncate(h);
            check(Files.size(root.resolve("append-partial")) == 0);
        }
    }
    private static void truncatePrefetch(Path root) throws Exception {
        Files.writeString(root.resolve("truncate-prefetch"), "abc\ndef");
        try (FileSession files = writable(root)) {
            FileSession.Handle h = files.open("truncate-prefetch", 3);
            check(Arrays.equals(files.getLine(h), utf8("abc\n")));
            files.truncate(h); check(Files.size(root.resolve("truncate-prefetch")) == 4);
            // Native ftruncate preserves buffered input and descriptor offset.
            check(Arrays.equals(files.read(h, 3), utf8("def")));
            files.flush(h); check(files.read(h, 1).length == 0);
            files.rewind(h); check(Arrays.equals(files.read(h, 10), utf8("abc\n")));
        }
        Files.writeString(root.resolve("truncate-prefetch-failure"), "abc\ndef");
        List<CountedChannel> channels = new ArrayList<>();
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 32, 100, 100), true, path -> {
            CountedChannel channel = new CountedChannel(path, true); channel.failRestoration = true;
            channels.add(channel); return channel;
        })) {
            FileSession.Handle h = files.open("truncate-prefetch-failure", 3);
            files.getLine(h);
            terminal(FileSession.Code.PROVIDER_FAILURE, () -> files.truncate(h));
            check(Files.size(root.resolve("truncate-prefetch-failure")) == 4);
            check(files.stats().liveHandles() == 1); h.close(); check(channels.get(0).closes == 1);
        }
    }
    private static void identifiedWriteErrorsAndCustody(Path root) throws Exception {
        for (int code : new int[]{28,30,122,22}) {
            String reason = switch (code) { case 28 -> "No space left on device"; case 30 -> "Read-only file system";
                case 122 -> "Disk quota exceeded"; default -> "Invalid argument"; };
            List<CountedChannel> channels = new ArrayList<>();
            FileSession files = new FileSession(root, Path.of("."), limits(1, 10, 10, 100), true, path -> {
                CountedChannel channel = new CountedChannel(path, true); channel.maxWrite = 1;
                channel.writeFailure = new IOException(reason); channels.add(channel); return channel;
            });
            FileSession.Handle h = files.open("partial", 3);
            guest(code, FileSession.Operation.WRITE, () -> files.write(h, new byte[]{33,34}));
            check(files.stats().bytesWritten() == 1 && Files.readAllBytes(root.resolve("partial"))[0] == 33);
            // fseek preserves ferror even after accepted output and an identified error.
            files.rewind(h); terminal(FileSession.Code.POLICY, () -> files.getLine(h));
            channels.get(0).closeFailure = new IOException("uncertain controlled close");
            h.close(); check(channels.get(0).closes == 1 && files.stats().liveHandles() == 1);
            terminal(FileSession.Code.PROVIDER_FAILURE, files::close);
            check(channels.get(0).closes == 1 && files.stats().bytesWritten() == 1);
        }
        FileSession.Limits noOp = new FileSession.Limits(1, 16, 16, 1, 4096, 16, 16);
        try (FileSession files = new FileSession(root, Path.of("."), noOp, true)) {
            FileSession.Handle first = files.open("partial", 0);
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.open("operation-refused", 1));
            check(!Files.exists(root.resolve("operation-refused"))); first.close();
        }
        try (FileSession files = new FileSession(root, Path.of("."), limits(1, 16, 16, 100), true)) {
            FileSession.Handle first = files.open("partial", 0);
            terminal(FileSession.Code.RESOURCE_LIMIT, () -> files.open("handle-refused", 1));
            check(!Files.exists(root.resolve("handle-refused"))); first.close();
        }
    }
    public static void main(String[] arguments) throws Exception {
        if (arguments.length != 1) throw new IllegalArgumentException("Pass a new test-root path");
        Path root = Path.of(arguments[0]).toAbsolutePath(); Files.createDirectory(root);
        try {
            metadataAndBytes(root); ownerAndTimestampDomains(root); pathsAndLimits(root); failuresAndRetirement(root); uncertainCloseCustody(root); stickyFileErrors(root); acquisitionCleanupFatalPriority(root); cancellation(root); writingModes(root); writingBudgetsAndFailures(root); identifiedWriteErrorsAndCustody(root); truncatePrefetch(root); appendLogicalCursor(root);
            System.out.println("FILE_SESSION_CHECKS " + checks);
        } finally {
            try (var paths = Files.walk(root)) {
                for (Path path : paths.sorted(java.util.Comparator.reverseOrder()).toList()) Files.deleteIfExists(path);
            }
        }
    }
}
