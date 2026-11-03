package ansatz.lean.jvm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/** Lossless, bounded Lean Name syntax. A Name supplies no native evidence authority. */
public final class LeanName {
    public enum Kind { ANONYMOUS, STRING, NUMBER }
    private static final int MAX_DEPTH = 64, MAX_LEAF = 1024, MAX_UNITS = 65536;
    private static final LeanName ANONYMOUS = new LeanName();
    private final Kind kind;
    private final LeanName parent;
    private final String text;
    private final BigInteger number;
    private final int depth, units, hash;

    private LeanName() {
        kind = Kind.ANONYMOUS; parent = null; text = null; number = null;
        depth = 1; units = 0; hash = 1;
    }
    private LeanName(Kind kind, LeanName parent, String text, BigInteger number) {
        this.parent = Objects.requireNonNull(parent, "parent");
        if (parent.depth >= MAX_DEPTH || parent.units > MAX_UNITS - text.length())
            throw new IllegalArgumentException("Lean Name exceeds depth or text bound");
        this.kind = kind; this.text = text; this.number = number;
        depth = parent.depth + 1; units = parent.units + text.length();
        hash = 31 * (31 * parent.hash + kind.ordinal()) + text.hashCode();
    }
    public static LeanName anonymous() { return ANONYMOUS; }
    public static LeanName str(LeanName parent, String part) {
        Objects.requireNonNull(part, "part");
        if (part.length() > MAX_LEAF) throw new IllegalArgumentException("Lean Name leaf exceeds bound");
        for (int i = 0; i < part.length(); i++) {
            char c = part.charAt(i);
            if (Character.isHighSurrogate(c)) {
                if (++i == part.length() || !Character.isLowSurrogate(part.charAt(i)))
                    throw new IllegalArgumentException("Lean Name requires valid UTF-16");
            } else if (Character.isLowSurrogate(c)) {
                throw new IllegalArgumentException("Lean Name requires valid UTF-16");
            }
        }
        return new LeanName(Kind.STRING, parent, part, null);
    }
    public static LeanName num(LeanName parent, BigInteger unsignedPart) {
        Objects.requireNonNull(unsignedPart, "unsignedPart");
        if (unsignedPart.getClass() != BigInteger.class || unsignedPart.signum() < 0 || unsignedPart.bitLength() > 64)
            throw new IllegalArgumentException("Lean Name number requires exact UInt64 BigInteger");
        return new LeanName(Kind.NUMBER, parent, unsignedPart.toString(), unsignedPart);
    }
    public Kind kind() { return kind; }
    public Optional<LeanName> parent() { return Optional.ofNullable(parent); }
    public String stringPart() {
        if (kind != Kind.STRING) throw new IllegalStateException("Not a string Name component");
        return text;
    }
    public BigInteger numberPart() {
        if (kind != Kind.NUMBER) throw new IllegalStateException("Not a numeric Name component");
        return number;
    }
    /** Deeply immutable JDK lists with the logical graph's lossless encoding. */
    public List<Object> toEdn() {
        LeanName[] path = new LeanName[depth - 1];
        LeanName n = this;
        for (int i = path.length - 1; i >= 0; i--) { path[i] = n; n = n.parent; }
        List<Object> result = List.of("anonymous");
        for (LeanName part : path)
            result = List.of(part.kind == Kind.STRING ? "str" : "num", result, part.text);
        return result;
    }
    /** Syntax validation and snapshot only; does not authenticate a declaration. */
    public static LeanName fromEdn(List<?> encoded) {
        Objects.requireNonNull(encoded, "encoded");
        List<String> kinds = new ArrayList<>(), leaves = new ArrayList<>();
        IdentityHashMap<List<?>, Boolean> seen = new IdentityHashMap<>();
        List<?> current = encoded;
        int units = 0;
        while (true) {
            if (seen.put(current, Boolean.TRUE) != null || seen.size() > MAX_DEPTH)
                throw new IllegalArgumentException("Cyclic or over-depth Lean Name");
            int size = current.size();
            if (size == 1 && "anonymous".equals(current.get(0))) break;
            if (size != 3 || !(current.get(0) instanceof String tag)
                    || !(tag.equals("str") || tag.equals("num"))
                    || !(current.get(1) instanceof List<?> next)
                    || !(current.get(2) instanceof String leaf))
                throw new IllegalArgumentException("Invalid Lean Name encoding");
            if (leaf.length() > MAX_LEAF || units > MAX_UNITS - leaf.length())
                throw new IllegalArgumentException("Lean Name text exceeds bound");
            units += leaf.length();
            if (tag.equals("num")) {
                if (leaf.isEmpty() || leaf.length() > 20 || (leaf.length() > 1 && leaf.charAt(0) == '0'))
                    throw new IllegalArgumentException("Noncanonical Lean Name number");
                for (int i = 0; i < leaf.length(); i++)
                    if (leaf.charAt(i) < '0' || leaf.charAt(i) > '9')
                        throw new IllegalArgumentException("Noncanonical Lean Name number");
            }
            kinds.add(tag); leaves.add(leaf); current = next;
        }
        LeanName result = anonymous();
        for (int i = kinds.size() - 1; i >= 0; i--)
            result = kinds.get(i).equals("str") ? str(result, leaves.get(i))
                    : num(result, new BigInteger(leaves.get(i)));
        return result;
    }
    @Override public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof LeanName n) || hash != n.hash || depth != n.depth) return false;
        LeanName a = this, b = n;
        while (a.kind != Kind.ANONYMOUS) {
            if (a.kind != b.kind || !a.text.equals(b.text)) return false;
            a = a.parent; b = b.parent;
        }
        return true;
    }
    @Override public int hashCode() { return hash; }
    /** Bounded diagnostic display, never an identity parser. */
    @Override public String toString() {
        StringBuilder out = new StringBuilder("LeanName[");
        LeanName[] path = new LeanName[depth - 1];
        LeanName n = this;
        for (int i = path.length - 1; i >= 0; i--) { path[i] = n; n = n.parent; }
        for (int p = 0; p < path.length; p++) {
            if (p > 0) out.append(',');
            LeanName part = path[p];
            out.append(part.kind == Kind.STRING ? "str(\"" : "num(");
            for (int i = 0; i < part.text.length(); i++) {
                if (out.length() >= 480) return out.append("…]").toString();
                char c = part.text.charAt(i);
                if (c == '\\' || c == '"') out.append('\\').append(c);
                else if (Character.isISOControl(c)) out.append('?');
                else if (Character.isHighSurrogate(c)) { out.append(c).append(part.text.charAt(++i)); }
                else out.append(c);
            }
            out.append(part.kind == Kind.STRING ? "\")" : ")");
            if (out.length() >= 480 && p + 1 < path.length) return out.append("…]").toString();
        }
        return out.append(']').toString();
    }
}
