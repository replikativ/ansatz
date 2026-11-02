package ansatz.lean.jvm;

import java.lang.reflect.Modifier;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;

/** Actual typed-core public-object tests. Handwritten plans grant no native admission. */
public final class PublicDatatypeChecks {
    private static int checks;
    private static final class ExecutableList extends java.util.AbstractList<Object> {
        @Override public Object get(int index) { throw new AssertionError("Custom list callback"); }
        @Override public int size() { throw new AssertionError("Custom list callback"); }
    }
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("Public datatype check " + checks); }
    private static void refused(Runnable action) {
        try { action.run(); throw new AssertionError("Invalid public value accepted"); }
        catch (IllegalArgumentException expected) { checks++; }
    }
    private static void immutable(Runnable action) {
        try { action.run(); throw new AssertionError("Mutable shared view"); }
        catch (UnsupportedOperationException expected) { checks++; }
    }
    private static Map<String,Object> m(Object... pairs) {
        Map<String,Object> out = new HashMap<>();
        for (int i = 0; i < pairs.length; i += 2) out.put((String) pairs[i], pairs[i + 1]); return out;
    }
    private static List<Object> name(String... parts) {
        List<Object> out = List.of("anonymous"); for (String part : parts) out = List.of("str", out, part); return out;
    }
    private static Map<String,Object> t(String kind) { return m("kind", kind); }
    private static Map<String,Object> field(String name, Object type) { return m("name", name(name), "type", type); }
    private static Map<String,Object> location(int field, int plan, Object location) { return m("index", field, "plan", plan, "location", location); }
    private static Map<String,Object> object(int slot) { return m("kind", "object", "slot", slot); }
    private static Map<String,Object> scalar(int offset, String lane) { return m("kind", "scalar", "offset", offset, "lane", lane); }
    private static Map<String,Object> node(int tag, int objects, int ssize) { return m("kind", "node", "tag", tag, "objects", objects, "usize", 0, "ssize", ssize); }
    private static Map<String,Object> ctor(int index, Object name, Object representation, Object fields) {
        return m("index", index, "name", name, "representation", representation, "fields", fields);
    }
    private static Map<String,Object> row(int id, Object type, String ir, Object encoding) { return m("id", id, "type", type, "closedIR", ir, "encoding", encoding); }
    private static Object scalarEncoding(String lane, String boxed) { return m("kind", "scalar", "lane", lane, "boxed", boxed); }
    private static String json(Object value) {
        if (value instanceof Map<?,?> map) {
            TreeMap<String,Object> ordered = new TreeMap<>(); map.forEach((key, item) -> ordered.put((String) key, item));
            List<String> entries = new ArrayList<>(); ordered.forEach((key, item) -> entries.add(json(key) + ":" + json(item)));
            return "{" + String.join(",", entries) + "}";
        }
        if (value instanceof List<?> list) {
            List<String> items = new ArrayList<>(); for (Object item : list) items.add(json(item)); return "[" + String.join(",", items) + "]";
        }
        if (value instanceof String s) return "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
        return value.toString();
    }
    private static String digest(Object document) throws Exception {
        return java.util.HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(json(document).getBytes(StandardCharsets.UTF_8)));
    }
    private static LeanType.Registry fixture() throws Exception {
        Object packet = m("kind", "nominal", "id", 0), box = m("kind", "nominal", "id", 1);
        Object nat = t("nat"), bytes = t("bytes"), unit = t("unit"), bool = t("bool"), character = t("char");
        Object i8 = m("kind", "machine-int", "bits", 8, "signed", true);
        Object u32 = m("kind", "machine-int", "bits", 32, "signed", false), f32 = m("kind", "float", "bits", 32);
        Object option = m("kind", "option", "element", unit), array = m("kind", "array", "element", nat);
        Object origin = m("module", name("PublicFixture"), "productSha256", "a".repeat(64));
        Object packetDef = m("id", 0, "origin", origin, "name", name("PublicFixture", "Packet"), "universes", List.of(), "arguments", List.of(),
                "constructors", List.of(m("name", name("PublicFixture", "Packet", "mk"), "fields", List.of(
                        field("count", nat), field("code", u32), field("payload", bytes), field("maybe", option),
                        field("values", array), field("alias", box), field("flag", bool), field("weight", f32), field("character", character), field("signed", i8)))));
        Object boxDef = m("id", 1, "origin", origin, "name", name("PublicFixture", "Box"), "universes", List.of(0), "arguments", List.of(nat),
                "constructors", List.of(m("name", name("PublicFixture", "Box", "mk"), "fields", List.of(field("value", nat)))));
        Map<String,Object> logical = m("schema", "lean-jvm-type-graph/3", "roots", List.of(packet), "definitions", List.of(packetDef, boxDef));
        Object packetCtor = ctor(0, name("PublicFixture", "Packet", "mk"), node(0, 5, 14), List.of(
                location(0, 1, object(0)), location(1, 2, scalar(0, "uint32")), location(2, 3, object(1)),
                location(3, 4, object(2)), location(4, 6, object(3)), location(5, 7, object(4)),
                location(6, 8, scalar(12, "uint8")), location(7, 9, scalar(4, "float32")), location(8, 10, scalar(8, "uint32")), location(9, 11, scalar(13, "uint8"))));
        Object none = ctor(0, name("Option", "none"), m("kind", "immediate", "tag", 0), List.of());
        Object some = ctor(1, name("Option", "some"), node(1, 1, 0), List.of(location(0, 5, object(0))));
        Object boxCtor = ctor(0, name("PublicFixture", "Box", "mk"), m("kind", "alias", "field", 0), List.of(location(0, 1, m("kind", "self"))));
        Map<String,Object> normalized = m("schema", "lean-jvm-typed-storage/1", "logicalDigest", digest(logical),
                "target", m("wordBits", 64, "byteOrder", "little", "storageAbi", "node-pure-data/1"), "roots", List.of(0), "plans", List.of(
                        row(0, packet, "object", m("kind", "family", "constructors", List.of(packetCtor))),
                        row(1, nat, "tobject", t("nat")), row(2, u32, "uint32", scalarEncoding("uint32", "small-immediate")),
                        row(3, bytes, "object", t("bytes")), row(4, option, "tobject", m("kind", "family", "constructors", List.of(none, some))),
                        row(5, unit, "tagged", t("unit")), row(6, array, "object", m("kind", "array", "element", 1)),
                        row(7, box, "tobject", m("kind", "family", "constructors", List.of(boxCtor))),
                        row(8, bool, "uint8", scalarEncoding("uint8", "small-immediate")),
                        row(9, f32, "float32", scalarEncoding("float32", "box32")),
                        row(10, character, "uint32", scalarEncoding("uint32", "small-immediate")),
                        row(11, i8, "uint8", scalarEncoding("uint8", "small-immediate"))));
        Class<?> interpreter = Class.forName("ansatz.lean.jvm.internal.exec.Interpreter");
        return ValueBridge.compileTrusted(interpreter, logical, normalized);
    }
    private static void surface() throws Exception {
        for (Class<?> type : List.of(LeanType.class, LeanData.class, LeanBytes.class, LeanType.Constructor.class, LeanType.Field.class)) {
            check(Modifier.isFinal(type.getModifiers()));
            for (var constructor : type.getDeclaredConstructors()) check(!Modifier.isPublic(constructor.getModifiers()));
            for (var field : type.getDeclaredFields()) check(!Modifier.isPublic(field.getModifiers()));
        }
        check(!Modifier.isPublic(ValueBridge.class.getModifiers()));
        check(LeanType.Constructor.class.getMethod("create", List.class).getReturnType() == LeanData.class);
        check(LeanData.class.getMethod("fields").getReturnType() == List.class);
        check(LeanBytes.class.getMethod("toByteArray").getReturnType() == byte[].class);
    }
    public static void main(String[] arguments) throws Exception {
        surface();
        if (Arrays.equals(arguments, new String[]{"--surface-only"})) {
            System.out.println("PublicDatatypeChecks surface-only: " + checks + " checks passed; core untested"); return;
        }
        check(arguments.length == 0);
        LeanType.Registry registry = fixture(); LeanType packet = registry.roots.get(0);
        LeanType.Constructor constructor = packet.constructors().get(0);
        check(packet.nominalId().orElseThrow().declaration().equals(LeanName.fromEdn(name("PublicFixture", "Packet"))));
        check(packet.constructor(constructor.name()) == constructor);
        check(constructor.fields().size() == 10 && constructor.fields().get(1).index() == 1);
        check(constructor.fields().get(1).type().bits() == 32 && !constructor.fields().get(1).type().signed());
        LeanType box = constructor.fields().get(5).type();
        check(box.arguments().get(0).kind() == LeanType.Kind.NAT && box.universes().equals(List.of(0)));
        LeanData alias = box.constructors().get(0).create(List.of(BigInteger.valueOf(99)));
        byte[] source = {0, -1, 7}; List<Object> array = new ArrayList<>(List.of(BigInteger.ONE, BigInteger.TEN));
        float nan = Float.intBitsToFloat(0x7fc01234);
        List<Object> fields = new ArrayList<>(List.of(BigInteger.valueOf(42), BigInteger.valueOf(0xffffffffL), source,
                Optional.of(LeanUnit.INSTANCE), array, alias, true, nan, 0x1f600, -1));
        LeanData value = constructor.create(fields);
        source[0] = 88; array.clear(); fields.clear();
        check(value.field(0).equals(BigInteger.valueOf(42)));
        check(value.field(1).equals(BigInteger.valueOf(0xffffffffL)));
        LeanBytes payload = (LeanBytes) value.field(2);
        check(payload.size() == 3 && payload.get(0) == 0 && payload.get(1) == 255);
        check(value.field(3).equals(Optional.of(LeanUnit.INSTANCE)));
        check(value.field(4).equals(List.of(BigInteger.ONE, BigInteger.TEN)));
        check(value.field(5).equals(alias)); check(value.field(6).equals(Boolean.TRUE));
        check(Float.floatToRawIntBits((Float) value.field(7)) == 0x7fc01234);
        check(value.field(8).equals(0x1f600));
        check(value.field(9).equals(BigInteger.valueOf(-1)));
        immutable(() -> value.fields().set(0, BigInteger.ZERO));
        immutable(() -> value.constructor().fields().clear());
        immutable(() -> packet.constructors().clear());
        @SuppressWarnings("unchecked") List<Object> sharedArray = (List<Object>) value.field(4);
        immutable(() -> sharedArray.set(0, BigInteger.ZERO));
        byte[] copied = payload.toByteArray(); copied[1] = 0; check(payload.get(1) == 255);
        LeanBytes standalone = LeanBytes.copyOf(new byte[]{0, -1, 7});
        check(standalone.equals(payload) && standalone.hashCode() == payload.hashCode());
        check(!standalone.equals(new byte[]{0, -1, 7}));
        LeanData reused = (LeanData) packet.create(value);
        check(reused.equals(value) && reused.hashCode() == value.hashCode());
        @SuppressWarnings("unchecked") Map<String,Object> materialized = (Map<String,Object>) packet.materialize(value);
        LeanData rebuilt = (LeanData) packet.create(materialized);
        check(rebuilt.equals(value) && rebuilt.hashCode() == value.hashCode());
        @SuppressWarnings("unchecked") List<Object> plainFields = (List<Object>) materialized.get("lean/fields");
        List<Object> alternate = new ArrayList<>(plainFields);
        alternate.set(7, Float.intBitsToFloat(0x7fc05678));
        Map<String,Object> alternateMap = new HashMap<>(materialized); alternateMap.put("lean/fields", alternate);
        LeanData otherNaN = (LeanData) packet.create(alternateMap);
        check(otherNaN.equals(value) && otherNaN.hashCode() == value.hashCode());
        check(Float.floatToRawIntBits((Float) otherNaN.field(7)) == 0x7fc05678);
        alternate.set(7, -0.0f); LeanData negativeZero = (LeanData) packet.create(alternateMap);
        alternate.set(7, 0.0f); LeanData positiveZero = (LeanData) packet.create(alternateMap);
        check(!negativeZero.equals(positiveZero));
        check(!value.equals(materialized));
        @SuppressWarnings("unchecked") List<Object> materialFields = (List<Object>) materialized.get("lean/fields");
        ((byte[]) materialFields.get(2))[0] = 100; check(payload.get(0) == 0);
        LeanType.Registry equivalent = fixture();
        check(equivalent.roots.get(0).create(value).equals(value));
        check(value.toString().length() < 2048 && standalone.toString().length() < 64);
        refused(() -> constructor.create(List.of()));
        refused(() -> packet.constructor(LeanName.str(LeanName.anonymous(), "missing")));
        refused(() -> constructor.fields().get(1).type().create(BigInteger.ONE.shiftLeft(32)));
        refused(() -> constructor.fields().get(6).type().create(2));
        refused(() -> constructor.fields().get(8).type().create(0xd800));
        refused(() -> constructor.fields().get(7).type().create(Double.valueOf(1)));
        refused(() -> constructor.fields().get(4).type().create(new ArrayList<>(List.of("bad"))));
        refused(() -> constructor.fields().get(4).type().create(new ExecutableList()));
        refused(() -> constructor.fields().get(4).type().create(java.util.Collections.unmodifiableList(new ExecutableList())));
        refused(() -> constructor.fields().get(4).type().create(new Object[100001]));
        refused(() -> constructor.fields().get(9).type().create(-129));
        List<Object> cycle = new ArrayList<>(); cycle.add(cycle);
        refused(() -> constructor.fields().get(4).type().create(cycle));
        refused(() -> LeanBytes.copyOf(new byte[1048577]));
        Map<String,Object> wrong = new HashMap<>(materialized); wrong.put("extra", "bad");
        refused(() -> packet.create(wrong));
        System.out.println("PublicDatatypeChecks: " + checks + " checks passed against actual core");
    }
}
