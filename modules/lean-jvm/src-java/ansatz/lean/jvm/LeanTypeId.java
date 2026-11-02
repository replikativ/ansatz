package ansatz.lean.jvm;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/** Detached nominal identity syntax. Matching an ID never grants layout or storage authority. */
public final class LeanTypeId {
    private final String definingProductSha256, semanticSha256;
    private final LeanName definingModule, declaration;

    public LeanTypeId(String definingProductSha256, LeanName definingModule,
                      LeanName declaration, String semanticSha256) {
        this.definingProductSha256 = digest(definingProductSha256);
        this.semanticSha256 = digest(semanticSha256);
        this.definingModule = nonanonymous(definingModule);
        this.declaration = nonanonymous(declaration);
    }
    private static String digest(String value) {
        Objects.requireNonNull(value, "digest");
        if (value.length() != 64) throw new IllegalArgumentException("Expected lowercase SHA-256 hex");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (!(c >= '0' && c <= '9' || c >= 'a' && c <= 'f'))
                throw new IllegalArgumentException("Expected lowercase SHA-256 hex");
        }
        return value;
    }
    private static LeanName nonanonymous(LeanName value) {
        Objects.requireNonNull(value, "Name");
        if (value.kind() == LeanName.Kind.ANONYMOUS)
            throw new IllegalArgumentException("Module and declaration Names must be nonanonymous");
        return value;
    }
    public String definingProductSha256() { return definingProductSha256; }
    public LeanName definingModule() { return definingModule; }
    public LeanName declaration() { return declaration; }
    public String semanticSha256() { return semanticSha256; }
    public Map<String,Object> toEdn() {
        return Map.of("productSha256", definingProductSha256, "module", definingModule.toEdn(),
                "name", declaration.toEdn(), "semanticSha256", semanticSha256);
    }
    /** Exact, data-only encoding; validates syntax, not native provenance. */
    public static LeanTypeId fromEdn(Map<String,?> encoded) {
        Objects.requireNonNull(encoded, "encoded");
        if (encoded.size() != 4) throw new IllegalArgumentException("Invalid LeanTypeId keys");
        for (Object key : encoded.keySet())
            if (!(key instanceof String s) || !(s.equals("productSha256") || s.equals("module")
                    || s.equals("name") || s.equals("semanticSha256")))
                throw new IllegalArgumentException("Invalid LeanTypeId keys");
        if (!(encoded.get("productSha256") instanceof String product)
                || !(encoded.get("semanticSha256") instanceof String semantic)
                || !(encoded.get("module") instanceof List<?> module)
                || !(encoded.get("name") instanceof List<?> name))
            throw new IllegalArgumentException("Invalid LeanTypeId encoding");
        return new LeanTypeId(product, LeanName.fromEdn(module), LeanName.fromEdn(name), semantic);
    }
    @Override public boolean equals(Object other) {
        return this == other || other instanceof LeanTypeId id
                && definingProductSha256.equals(id.definingProductSha256)
                && definingModule.equals(id.definingModule) && declaration.equals(id.declaration)
                && semanticSha256.equals(id.semanticSha256);
    }
    @Override public int hashCode() {
        int h = definingProductSha256.hashCode();
        h = 31 * h + definingModule.hashCode(); h = 31 * h + declaration.hashCode();
        return 31 * h + semanticSha256.hashCode();
    }
    @Override public String toString() {
        return "LeanTypeId[product=" + definingProductSha256 + ",module=" + definingModule
                + ",name=" + declaration + ",semantic=" + semanticSha256 + "]";
    }
}
