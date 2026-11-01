package ansatz.lean.jvm;

/** Bounded value-only failure details. Does not expose guest runtime owners. */
public final class LeanException extends RuntimeException {
    private final String code;
    private final String category;

    LeanException(String code, String category, String message) {
        super(message);
        this.code = code;
        this.category = category;
    }

    public String code() { return code; }
    public String category() { return category; }
}
