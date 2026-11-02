package ansatz.lean.jvm;

/** Digest values for a completed artifact export, not an execution/admission token.
 * Keep manifestSHA256 separately in trusted application configuration. */
public final class PreparedArtifact {
    private final String manifestSHA256;
    private final String archiveSHA256;

    PreparedArtifact(String manifestSHA256, String archiveSHA256) {
        this.manifestSHA256 = digest(manifestSHA256);
        this.archiveSHA256 = digest(archiveSHA256);
    }

    private static String digest(String value) {
        if (value == null || !value.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException("Preparation returned an invalid SHA-256 digest");
        }
        return value;
    }

    public String manifestSHA256() { return manifestSHA256; }
    public String archiveSHA256() { return archiveSHA256; }
}
