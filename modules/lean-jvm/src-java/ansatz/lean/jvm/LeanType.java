package ansatz.lean.jvm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/** Detached closed type issued by the SDK's trusted native-plan integration. */
public final class LeanType {
    public enum Kind { NAT, INT, BOOL, STRING, UNIT, CHAR, BYTES, MACHINE_INT, WORD, FLOAT,
                       OPTION, LIST, ARRAY, PRODUCT, SUM, EXCEPT, NOMINAL }
    final Registry registry;
    final int plan;
    final Map<String,Object> row;
    final Map<String,Object> logical;
    private final Kind kind;
    private final LeanTypeId id;
    private final String digest;
    private List<Constructor> constructors;

    LeanType(Registry registry, int plan, Map<String,Object> row, String digest) {
        this.registry = registry; this.plan = plan; this.row = row; this.digest = digest;
        logical = ValueBridge.map(row.get("type"));
        kind = Kind.valueOf(((String) logical.get("kind")).replace('-', '_').toUpperCase(java.util.Locale.ROOT));
        if (kind == Kind.NOMINAL) {
            Map<String,Object> definition = registry.definitions.get(ValueBridge.integer(logical.get("id")));
            Map<String,Object> origin = ValueBridge.map(definition.get("origin"));
            id = new LeanTypeId((String) origin.get("productSha256"),
                    LeanName.fromEdn(ValueBridge.list(origin.get("module"))),
                    LeanName.fromEdn(ValueBridge.list(definition.get("name"))), digest);
        } else id = null;
    }
    public Kind kind() { return kind; }
    public Optional<LeanTypeId> nominalId() { return Optional.ofNullable(id); }
    public List<LeanType> arguments() {
        List<Object> arguments;
        if (kind == Kind.NOMINAL) arguments = ValueBridge.list(definition().get("arguments"));
        else arguments = switch (kind) {
            case OPTION, LIST, ARRAY -> List.of(logical.get("element"));
            case PRODUCT -> List.of(logical.get("first"), logical.get("second"));
            case SUM -> List.of(logical.get("left"), logical.get("right"));
            case EXCEPT -> List.of(logical.get("error"), logical.get("value"));
            default -> List.of();
        };
        List<LeanType> result = new ArrayList<>(arguments.size());
        for (Object argument : arguments) result.add(registry.resolve(ValueBridge.map(argument)));
        return List.copyOf(result);
    }
    public List<Integer> universes() {
        if (kind != Kind.NOMINAL) return List.of();
        List<Integer> result = new ArrayList<>();
        for (Object level : ValueBridge.list(definition().get("universes"))) result.add(ValueBridge.integer(level));
        return List.copyOf(result);
    }
    public int bits() {
        if (kind == Kind.WORD) return 64;
        if (kind != Kind.MACHINE_INT && kind != Kind.FLOAT) throw new IllegalStateException("Type has no bit width");
        return ValueBridge.integer(logical.get("bits"));
    }
    public boolean signed() {
        if (kind != Kind.MACHINE_INT && kind != Kind.WORD) throw new IllegalStateException("Type has no signedness");
        return (Boolean) logical.get("signed");
    }
    public List<Constructor> constructors() {
        if (kind != Kind.NOMINAL) throw new IllegalStateException("Builtin types use their host carriers");
        return constructors;
    }
    public Constructor constructor(LeanName name) {
        java.util.Objects.requireNonNull(name, "constructor Name");
        for (Constructor constructor : constructors()) if (constructor.name.equals(name)) return constructor;
        throw new IllegalArgumentException("Constructor is not a member of this type");
    }
    /**
     * Construct canonical immutable storage now, reusing compatible typed children.
     * Ordinary inputs use Java carriers; the Clojure facade converts language tags,
     * nil and numeric carriers under this type before construction. Exact standard
     * JDK collections and Clojure persistent vectors/maps are supported; custom,
     * lazy or delegating adapters are refused rather than executing their getters.
     */
    public Object create(Object hostValue) { return bridge().construct(this, hostValue); }
    public Object materialize(Object typedValue) { return ValueBridge.materialize(this, typedValue); }
    ValueBridge bridge() { return registry.bridge; }
    String digest() { return digest; }
    Map<String,Object> definition() { return registry.definitions.get(ValueBridge.integer(logical.get("id"))); }
    List<Constructor> alternatives() { return constructors; }
    Constructor constructorAt(int index) { return constructors.get(index); }
    @Override public boolean equals(Object other) {
        return this == other || other instanceof LeanType type && digest.equals(type.digest)
                && java.util.Objects.equals(id, type.id);
    }
    @Override public int hashCode() { return 31 * digest.hashCode() + java.util.Objects.hashCode(id); }
    @Override public String toString() { return id == null ? "LeanType[" + kind + "]" : "LeanType[" + id + "]"; }

    public static final class Constructor {
        private final LeanType type;
        private final LeanName name;
        private final int index;
        private final List<Field> fields;
        Constructor(LeanType type, LeanName name, int index, List<Field> fields) {
            this.type = type; this.name = name; this.index = index; this.fields = List.copyOf(fields);
        }
        public LeanType type() { return type; }
        public LeanName name() { return name; }
        public int index() { return index; }
        public List<Field> fields() { return fields; }
        public LeanData create(List<?> orderedFields) {
            if (type.kind != Kind.NOMINAL) throw new IllegalStateException("Builtin types use their host carriers");
            return (LeanData) type.bridge().constructConstructor(this, orderedFields);
        }
    }
    public static final class Field {
        private final LeanName name;
        private final LeanType type;
        private final int index;
        Field(LeanName name, LeanType type, int index) { this.name = name; this.type = type; this.index = index; }
        public LeanName name() { return name; }
        public LeanType type() { return type; }
        public int index() { return index; }
    }
    /** Finite schema only: no registry entry can contain a runtime payload. */
    static final class Registry {
        final ValueBridge bridge;
        final Object schema;
        final Map<Integer,Map<String,Object>> definitions = new HashMap<>();
        final Map<Integer,LeanType> types = new HashMap<>();
        final Map<Map<String,Object>,LeanType> byLogical = new HashMap<>();
        final List<LeanType> roots;
        Registry(ValueBridge bridge, Object schema, Map<String,Object> metadata) {
            this.bridge = bridge; this.schema = schema;
            Map<String,Object> graph = ValueBridge.map(metadata.get("logical"));
            Map<String,Object> normalized = ValueBridge.map(metadata.get("normalized"));
            for (Object value : ValueBridge.list(graph.get("definitions"))) {
                Map<String,Object> definition = ValueBridge.map(value);
                definitions.put(ValueBridge.integer(definition.get("id")), definition);
            }
            Map<?,?> digests = (Map<?,?>) metadata.get("typeDigests");
            for (Object value : ValueBridge.list(normalized.get("plans"))) {
                Map<String,Object> row = ValueBridge.map(value);
                int index = ValueBridge.integer(row.get("id"));
                String digest = (String) digests.get(index);
                if (digest == null) digest = (String) digests.get((long) index);
                if (digest == null) throw new IllegalArgumentException("Missing detached type digest");
                LeanType type = new LeanType(this, index, row, digest);
                types.put(index, type); byLogical.put(type.logical, type);
            }
            for (LeanType type : types.values()) {
                List<Constructor> constructors = new ArrayList<>();
                Map<String,Object> encoding = ValueBridge.map(type.row.get("encoding"));
                if ("family".equals(encoding.get("kind"))) {
                    List<Object> rows = ValueBridge.list(encoding.get("constructors"));
                    for (Object value : rows) {
                        Map<String,Object> row = ValueBridge.map(value);
                        int index = ValueBridge.integer(row.get("index"));
                        List<Object> names = type.kind == Kind.NOMINAL
                                ? ValueBridge.list(ValueBridge.map(ValueBridge.list(type.definition().get("constructors")).get(index)).get("fields")) : List.of();
                        List<Field> fields = new ArrayList<>();
                        for (Object fieldValue : ValueBridge.list(row.get("fields"))) {
                            Map<String,Object> field = ValueBridge.map(fieldValue);
                            int position = ValueBridge.integer(field.get("index"));
                            LeanName name = type.kind == Kind.NOMINAL
                                    ? LeanName.fromEdn(ValueBridge.list(ValueBridge.map(names.get(position)).get("name")))
                                    : LeanName.anonymous();
                            fields.add(new Field(name, types.get(ValueBridge.integer(field.get("plan"))), position));
                        }
                        constructors.add(new Constructor(type, LeanName.fromEdn(ValueBridge.list(row.get("name"))), index, fields));
                    }
                }
                type.constructors = List.copyOf(constructors);
            }
            List<LeanType> selected = new ArrayList<>();
            for (Object root : ValueBridge.list(normalized.get("roots"))) selected.add(types.get(ValueBridge.integer(root)));
            roots = List.copyOf(selected);
        }
        LeanType resolve(Map<String,Object> logical) {
            LeanType result = byLogical.get(logical);
            if (result == null) throw new IllegalArgumentException("Closed type is absent from the admitted plan");
            return result;
        }
    }
}
