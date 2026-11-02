package ansatz.lean.jvm.internal.exec;

import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;
import java.util.Objects;
import ansatz.lean.jvm.internal.exec.Interpreter.Node;

/** Internal, independently authenticated filesystem constructor authority.
 * The witness wrappers are compiler fixtures, not original runtime factories.
 * No native service, allocation ownership or public custom-value codec is issued.
 */
public final class FilesystemLayouts {
    public static final String WITNESS_SHA256 = "f3b8877da4c477e04ea47adff3ce2cecae51cdf901a28cee54ca4f272f2195f9";
    private static final int WITNESS_BYTES = 66365;
    private static final int MAX_STRING_UNITS = 65536;
    private static final int MAX_INTERNAL_STRING_UNITS = 16 * 1024 * 1024;

    /** Allocate one fresh owned, plain Node, accounting it in the engine journal.
     * Failed compound allocations remain the caller's journal obligations.
     */
    @FunctionalInterface
    public interface Allocator {
        Node allocate(int tag, int objectFields, int scalarBytes);
    }

    private FilesystemLayouts() { }

    /** Only the exact frozen native capture issues this immutable authority.
     * No caller maps, parsed tags or self-reported hashes authorize layouts.
     */
    public static FilesystemLayouts authenticate(byte[] capture) {
        if (capture == null || capture.length != WITNESS_BYTES)
            throw new IllegalArgumentException("Filesystem layout witness extent differs");
        byte[] snapshot = capture.clone();
        try {
            String digest = HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(snapshot));
            if (!WITNESS_SHA256.equals(digest))
                throw new IllegalArgumentException("Filesystem layout witness differs");
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException("SHA-256 unavailable", impossible);
        }
        return new FilesystemLayouts();
    }

    private static void need(boolean condition, String message) {
        if (!condition) throw new IllegalArgumentException(message);
    }
    private static void text(String value) {
        text(value, MAX_STRING_UNITS);
    }
    private static void text(String value, int maximumUnits) {
        need(value != null && value.length() <= maximumUnits, "Bounded filesystem String required");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (Character.isHighSurrogate(c)) {
                need(++i < value.length() && Character.isLowSurrogate(value.charAt(i)), "Malformed filesystem String");
            } else need(!Character.isLowSurrogate(c), "Malformed filesystem String");
        }
    }
    private static Node node(Allocator allocator, int tag, int fields, int scalars) {
        Node value = Objects.requireNonNull(allocator.allocate(tag, fields, scalars), "Allocator result");
        need(value.tag == tag && value.rc == 1 && value.fields.length == fields && value.scalars.length == scalars,
                "Filesystem allocator returned another layout");
        return value;
    }
    private static void bits(Node value, int offset, int width, long raw) {
        for (int i = 0; i < width; i++) value.scalars[offset + i] = (byte) (raw >>> (8 * i));
    }
    private static Node time(Allocator allocator, long seconds, int nanos) {
        // systemTime: ctor_0.0.4, object slot 0; sset[1,0] UInt32.
        Node value = node(allocator, 0, 1, 4);
        value.fields[0] = Long.valueOf(seconds);
        bits(value, 0, 4, nanos);
        return value;
    }

    /** Signed Int seconds, nanos in [0,10^9), raw UInt64 size/link bit patterns.
     * The host provider separately imposes its supported nonnegative domains.
     */
    public Node metadata(Allocator allocator, long accessedSeconds, int accessedNanos,
                         long modifiedSeconds, int modifiedNanos, long sizeBits, long linksBits, int fileType) {
        Objects.requireNonNull(allocator, "allocator");
        need(accessedNanos >= 0 && accessedNanos < 1_000_000_000
                && modifiedNanos >= 0 && modifiedNanos < 1_000_000_000, "Invalid filesystem nanoseconds");
        need(fileType >= 0 && fileType <= 3, "Invalid filesystem FileType");
        Node accessed = time(allocator, accessedSeconds, accessedNanos);
        Node modified = time(allocator, modifiedSeconds, modifiedNanos);
        // metadata: ctor_0.0.17, sset[2,0] size, [2,16] type, [2,8] links.
        Node value = node(allocator, 0, 2, 17);
        value.fields[0] = accessed; value.fields[1] = modified;
        bits(value, 0, 8, sizeBits); bits(value, 8, 8, linksBits); bits(value, 16, 1, fileType);
        return value;
    }

    private static int errorTag(String kind) {
        need(kind != null, "IO.Error kind required");
        // Exact ctorInfo cidx values in the hash-authenticated fixture.
        return switch (kind) {
            case "alreadyExists" -> 0;
            case "otherError" -> 1;
            case "resourceBusy" -> 2;
            case "resourceVanished" -> 3;
            case "unsupportedOperation" -> 4;
            case "hardwareFault" -> 5;
            case "unsatisfiedConstraints" -> 6;
            case "illegalOperation" -> 7;
            case "protocolError" -> 8;
            case "timeExpired" -> 9;
            case "interrupted" -> 10;
            case "noFileOrDirectory" -> 11;
            case "invalidArgument" -> 12;
            case "permissionDenied" -> 13;
            case "resourceExhausted" -> 14;
            case "inappropriateType" -> 15;
            case "noSuchThing" -> 16;
            case "unexpectedEof" -> 17;
            case "userError" -> 18;
            default -> throw new IllegalArgumentException("Unknown IO.Error kind");
        };
    }
    private static int checkedError(String kind, String path, long code, String message) {
        int tag = errorTag(kind);
        need(code >= 0 && code <= 0xffff_ffffL, "IO.Error code must be UInt32");
        if (tag == 17) {
            need(path == null && code == 0 && message == null, "unexpectedEof has no payload");
        } else {
            text(message);
            if (tag == 18) need(path == null && code == 0, "userError has only a message");
            else if (tag == 10 || tag == 11) text(path);
            else if (tag == 0 || tag >= 12) { if (path != null) text(path); }
            else need(path == null, "This IO.Error kind has no filename");
        }
        return tag;
    }
    private static Object buildError(Allocator allocator, int tag, String path, long code, String message) {
        if (tag == 17) return Long.valueOf(17); // witnessed immediate ctor_17.
        if (tag == 18) {
            Node value = node(allocator, 18, 1, 0); value.fields[0] = message; return value;
        }
        boolean filename = tag == 0 || tag >= 10;
        Object name = path;
        if (filename && tag != 10 && tag != 11) {
            if (path == null) name = Long.valueOf(0); // Option.none
            else { Node some = node(allocator, 1, 1, 0); some.fields[0] = path; name = some; }
        }
        Node value = node(allocator, tag, filename ? 2 : 1, 4);
        if (filename) { value.fields[0] = name; value.fields[1] = message; }
        else value.fields[0] = message;
        // Every code fixture uses sset[objectFieldCount,0] UInt32.
        bits(value, 0, 4, code);
        return value;
    }

    /** One owned IO.Error payload; null optional path differs from some empty.
     * unexpectedEof requires null message/path and code zero. userError requires
     * only message, with null path/code zero. All validation precedes allocation.
     */
    public Object errorPayload(Allocator allocator, String kind, String path, long code, String message) {
        Objects.requireNonNull(allocator, "allocator");
        int tag = checkedError(kind, path, code, message);
        return buildError(allocator, tag, path, code, message);
    }

    /** An IO error envelope with its owned error payload. */
    public Node ioFailure(Allocator allocator, String kind, String path, long code, String message) {
        Objects.requireNonNull(allocator, "allocator");
        int tag = checkedError(kind, path, code, message);
        Object payload = buildError(allocator, tag, path, code, message);
        Node envelope = node(allocator, 1, 1, 0); envelope.fields[0] = payload; return envelope;
    }

    /** Transfer the caller's one owned guest result into the witnessed EST.Out.ok.
     * Nodes/credits must already belong to the actual engine; this helper does
     * not grant ownership, authenticate foreign Nodes, retain or release values.
     */
    public Node ioSuccess(Allocator allocator, Object value) {
        Objects.requireNonNull(allocator, "allocator");
        need(value != null && (value instanceof Node || value.getClass() == Long.class
                || value.getClass() == BigInteger.class || value.getClass() == String.class),
                "Actual guest result carrier required");
        // Internal IO Strings are not constrained by the public scalar-result
        // codec or diagnostic/path cap. The engine separately bounds UTF-8
        // output allocation before publishing a filesystem line result.
        if (value instanceof String) text((String) value, MAX_INTERNAL_STRING_UNITS);
        Node envelope = node(allocator, 0, 1, 0); envelope.fields[0] = value; return envelope;
    }
}
