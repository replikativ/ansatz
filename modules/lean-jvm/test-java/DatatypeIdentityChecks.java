package ansatz.lean.jvm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/** Standalone syntax/immutability checks; no interpreter or native admission. */
public final class DatatypeIdentityChecks {
    private static int checks;
    private static void check(boolean condition) {
        checks++; if (!condition) throw new AssertionError("Datatype identity check " + checks);
    }
    private static void refused(Runnable action) {
        try { action.run(); throw new AssertionError("Invalid identity accepted"); }
        catch (IllegalArgumentException expected) { checks++; }
    }
    private static void immutable(Runnable action) {
        try { action.run(); throw new AssertionError("Mutable identity encoding"); }
        catch (UnsupportedOperationException expected) { checks++; }
    }
    private static void wrongKind(Runnable action) {
        try { action.run(); throw new AssertionError("Wrong component accessor accepted"); }
        catch (IllegalStateException expected) { checks++; }
    }
    private static final class ForeignInteger extends BigInteger {
        private static final long serialVersionUID = 1L;
        ForeignInteger() { super("1"); }
        @Override public String toString() { throw new AssertionError("Foreign numeric callback"); }
    }
    private static final class ForeignValue {
        @Override public int hashCode() { throw new AssertionError("Unexpected input hashing"); }
        @Override public String toString() { throw new AssertionError("Unexpected input formatting"); }
        @Override public boolean equals(Object other) { throw new AssertionError("Unexpected input equality"); }
    }
    public static void main(String[] args) {
        check(args.length == 0);
        LeanName anon = LeanName.anonymous();
        check(anon.kind() == LeanName.Kind.ANONYMOUS && anon.parent().isEmpty());
        check(anon.toEdn().equals(List.of("anonymous")));
        wrongKind(anon::stringPart); wrongKind(anon::numberPart);
        LeanName dotted = LeanName.str(anon, "A.B");
        LeanName segmented = LeanName.str(LeanName.str(anon, "A"), "B");
        check(!dotted.equals(segmented));
        check(!LeanName.num(anon, BigInteger.ONE).equals(LeanName.str(anon, "1")));
        check(LeanName.str(anon, "").stringPart().isEmpty());
        LeanName unicode = LeanName.str(segmented, "λ😀\0\n");
        check(LeanName.fromEdn(unicode.toEdn()).equals(unicode));
        check(LeanName.fromEdn(unicode.toEdn()).hashCode() == unicode.hashCode());
        check(unicode.parent().orElseThrow().equals(segmented));
        wrongKind(unicode::numberPart);
        BigInteger max = BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE);
        LeanName maxName = LeanName.num(unicode, max);
        check(maxName.numberPart().equals(max));
        check(LeanName.fromEdn(maxName.toEdn()).equals(maxName));
        wrongKind(maxName::stringPart);
        refused(() -> LeanName.num(anon, BigInteger.valueOf(-1)));
        refused(() -> LeanName.num(anon, max.add(BigInteger.ONE)));
        refused(() -> LeanName.num(anon, new ForeignInteger()));
        for (String bad : List.of("", "00", "01", "-1", "+1", " 1", "1.0", "١", "18446744073709551616", "0".repeat(21)))
            refused(() -> LeanName.fromEdn(List.of("num", List.of("anonymous"), bad)));
        for (String bad : List.of("\uD800", "\uDC00", "a\uD800b"))
            refused(() -> LeanName.str(anon, bad));
        refused(() -> LeanName.str(anon, "x".repeat(1025)));
        refused(() -> LeanName.fromEdn(List.of("str", List.of("anonymous"), "\uD800")));
        refused(() -> LeanName.fromEdn(List.of("str", List.of("anonymous"), new ForeignValue())));
        refused(() -> LeanName.fromEdn(List.of(new ForeignValue())));
        for (List<?> bad : List.of(List.of(), List.of("anonymous", "extra"), List.of("str"),
                List.of("wat", List.of("anonymous"), "x"), List.of("str", "parent", "x")))
            refused(() -> LeanName.fromEdn(bad));
        List<Object> cyclic = new ArrayList<>(); cyclic.add("str"); cyclic.add(cyclic); cyclic.add("x");
        refused(() -> LeanName.fromEdn(cyclic));
        LeanName deepest = anon;
        for (int i = 0; i < 63; i++) deepest = LeanName.str(deepest, "x".repeat(1024));
        check(LeanName.fromEdn(deepest.toEdn()).equals(deepest));
        check(deepest.toString().length() < 512);
        LeanName full = deepest;
        refused(() -> LeanName.str(full, ""));
        refused(() -> LeanName.fromEdn(List.of("str", full.toEdn(), "")));
        List<Object> mutableParent = new ArrayList<>(List.of("anonymous"));
        List<Object> mutableName = new ArrayList<>(List.of("str", mutableParent, "Original"));
        LeanName snapshot = LeanName.fromEdn(mutableName);
        mutableName.set(2, "Changed"); mutableParent.clear();
        check(snapshot.equals(LeanName.str(anon, "Original")));
        immutable(() -> snapshot.toEdn().set(0, "num"));
        @SuppressWarnings("unchecked") List<Object> exportedParent = (List<Object>) snapshot.toEdn().get(1);
        immutable(() -> exportedParent.add("bad"));

        String a = "a".repeat(64), b = "b".repeat(64);
        LeanTypeId id = new LeanTypeId(a, segmented, unicode, b);
        check(id.definingProductSha256().equals(a) && id.semanticSha256().equals(b));
        check(id.definingModule().equals(segmented) && id.declaration().equals(unicode));
        check(LeanTypeId.fromEdn(id.toEdn()).equals(id));
        check(LeanTypeId.fromEdn(id.toEdn()).hashCode() == id.hashCode());
        check(!id.equals(new LeanTypeId(b, segmented, unicode, b)));
        check(!id.equals(new LeanTypeId(a, unicode, unicode, b)));
        check(!id.equals(new LeanTypeId(a, segmented, segmented, b)));
        check(!id.equals(new LeanTypeId(a, segmented, unicode, a)));
        check(!id.equals(id.toEdn()));
        check(new LeanTypeId(a, full, full, b).toString().length() < 1200);
        refused(() -> new LeanTypeId(a, anon, unicode, b));
        refused(() -> new LeanTypeId(a, segmented, anon, b));
        for (String bad : List.of("", "a".repeat(63), "a".repeat(65), "A".repeat(64), "g".repeat(64), "é".repeat(64))) {
            refused(() -> new LeanTypeId(bad, segmented, unicode, b));
            refused(() -> new LeanTypeId(a, segmented, unicode, bad));
        }
        Map<String,Object> mutableId = new HashMap<>(id.toEdn());
        List<Object> nameParts = new ArrayList<>(List.of("str", List.of("anonymous"), "Saved"));
        mutableId.put("name", nameParts);
        LeanTypeId saved = LeanTypeId.fromEdn(mutableId);
        nameParts.clear(); mutableId.clear();
        check(saved.declaration().equals(LeanName.str(anon, "Saved")));
        immutable(() -> id.toEdn().put("name", List.of("anonymous")));
        Map<String,Object> bad = new HashMap<>(id.toEdn()); bad.put("extra", a);
        refused(() -> LeanTypeId.fromEdn(bad));
        bad.remove("extra"); bad.remove("name"); bad.put("wrong", a);
        refused(() -> LeanTypeId.fromEdn(bad));
        bad.clear(); bad.putAll(id.toEdn()); bad.put("module", List.of("anonymous"));
        refused(() -> LeanTypeId.fromEdn(bad));
        bad.put("module", new ForeignValue());
        refused(() -> LeanTypeId.fromEdn(bad));
        bad.put("module", segmented.toEdn()); bad.put("semanticSha256", new ForeignValue());
        refused(() -> LeanTypeId.fromEdn(bad));
        System.out.println("DatatypeIdentityChecks: " + checks + " checks passed");
    }
}
