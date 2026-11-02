package ansatz.lean.jvm;

import java.util.Map;

/** Bounded value-only failure details. Does not expose guest runtime owners. */
public final class LeanException extends RuntimeException {
    private final String code;
    private final String category;
    private final Map<String, Object> details;

    LeanException(String code, String category, String message) {
        this(code, category, message, Map.of());
    }

    LeanException(String code, String category, String message, Object details) {
        super(message);
        this.code = code;
        this.category = category;
        this.details = "GuestIOError".equals(code) ? ioDetails(details) : Map.of();
    }

    // Accept only our standard immutable value carrier, never an arbitrary Map
    // implementation whose accessors could run code or retain guest owners.
    static Map<String, Object> ioDetails(Object candidate) {
        if (candidate == null || candidate.getClass() != Map.of("kind", "userError", "message", "").getClass())
            return Map.of();
        Map<?, ?> map = (Map<?, ?>) candidate;
        if (map.size() != 2 && map.size() != 3) return Map.of();
        Object kind = map.get("kind"), message = map.get("message"), truncated = map.get("messageTruncated");
        if (!"userError".equals(kind) || message == null || message.getClass() != String.class
                || (map.size() == 3 && !Boolean.TRUE.equals(truncated))) return Map.of();
        String text = (String) message;
        boolean clipped = text.length() > 2048;
        int end = Math.min(text.length(), 2048);
        if (clipped && end > 0 && Character.isHighSurrogate(text.charAt(end - 1))) end--;
        text = text.substring(0, end);
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            if (Character.isHighSurrogate(c)) {
                if (++i >= text.length() || !Character.isLowSurrogate(text.charAt(i))) return Map.of();
            } else if (Character.isLowSurrogate(c)) return Map.of();
        }
        return clipped || Boolean.TRUE.equals(truncated)
                ? Map.of("kind", "userError", "message", text, "messageTruncated", true)
                : Map.of("kind", "userError", "message", text);
    }

    /** Partial IO.Error projection: currently authenticated userError messages only. */
    public Map<String, Object> details() { return details; }
    public String code() { return code; }
    public String category() { return category; }
}
