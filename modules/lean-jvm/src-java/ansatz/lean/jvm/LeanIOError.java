package ansatz.lean.jvm;

/** An explicit synchronous host IO failure. Only the witnessed alternatives
 * below are supported; ordinary host exceptions remain terminal HostFailure. */
public final class LeanIOError extends RuntimeException {
    private final String kind;
    private LeanIOError(String kind, String message) {
        super(message); this.kind = kind;
    }
    public static LeanIOError userError(String message) {
        java.util.Objects.requireNonNull(message, "message");
        if (message.length() > 65536) throw new IllegalArgumentException("IO error message exceeds profile");
        for (int i = 0; i < message.length(); i++) {
            char c = message.charAt(i);
            if (Character.isHighSurrogate(c)) {
                if (++i >= message.length() || !Character.isLowSurrogate(message.charAt(i)))
                    throw new IllegalArgumentException("Malformed IO error message");
            } else if (Character.isLowSurrogate(c)) throw new IllegalArgumentException("Malformed IO error message");
        }
        return new LeanIOError("userError", message);
    }
    public static LeanIOError unexpectedEof() { return new LeanIOError("unexpectedEof", null); }
    public String kind() { return kind; }
}
