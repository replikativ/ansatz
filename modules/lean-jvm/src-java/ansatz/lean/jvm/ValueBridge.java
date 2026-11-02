package ansatz.lean.jvm;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.math.BigInteger;
import java.util.AbstractList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Optional;
import java.util.RandomAccess;

/** Trusted static seam only. No bundle, descriptor or view retains an engine. */
final class ValueBridge {
    private static final int MAX_ITEMS = 100000, MAX_DEPTH = 1024;
    // Optional trusted library classes, never a compile-time Clojure dependency.
    private static final Class<?> CLOJURE_VECTOR = optionalClass("clojure.lang.PersistentVector");
    private static final Class<?> CLOJURE_ARRAY_MAP = optionalClass("clojure.lang.PersistentArrayMap");
    private static final Class<?> CLOJURE_HASH_MAP = optionalClass("clojure.lang.PersistentHashMap");
    private static Class<?> optionalClass(String name) {
        try { return Class.forName(name, false, ValueBridge.class.getClassLoader()); }
        catch (ClassNotFoundException absent) { return null; }
    }
    private static final ClassValue<ValueBridge> BUNDLES = new ClassValue<>() {
        @Override protected ValueBridge computeValue(Class<?> type) { return new ValueBridge(type); }
    };
    private final Class<?> cohort;
    private final MethodHandle compile, describe, construct, copyBytes, freeze, child, constructorIndex,
            size, scalar, byteAt, copyBytesOut, prepare;
    private ValueBridge(Class<?> cohort) {
        this.cohort = cohort;
        if (!cohort.getName().equals("ansatz.lean.jvm.internal.exec.Interpreter"))
            throw new IllegalArgumentException("Expected the actual Interpreter cohort");
        try {
            MethodHandles.Lookup lookup = MethodHandles.privateLookupIn(cohort, MethodHandles.lookup());
            compile = lookup.findStatic(cohort, "valueCompileSchema", MethodType.methodType(Object.class, Map.class, Map.class));
            describe = lookup.findStatic(cohort, "valueDescribeSchema", MethodType.methodType(Map.class, Object.class));
            construct = lookup.findStatic(cohort, "valueConstruct", MethodType.methodType(Object.class, Object.class, int.class, Object.class));
            copyBytes = lookup.findStatic(cohort, "valueCopyBytes", MethodType.methodType(Object.class, byte[].class));
            freeze = lookup.findStatic(cohort, "valueFreeze", MethodType.methodType(Object.class, Object.class, int.class, Object.class, String.class));
            child = lookup.findStatic(cohort, "valueReadChild", MethodType.methodType(Object.class, Object.class, int.class));
            constructorIndex = lookup.findStatic(cohort, "valueConstructorIndex", MethodType.methodType(int.class, Object.class));
            size = lookup.findStatic(cohort, "valueSize", MethodType.methodType(int.class, Object.class));
            scalar = lookup.findStatic(cohort, "valueScalar", MethodType.methodType(Object.class, Object.class));
            byteAt = lookup.findStatic(cohort, "valueByteAt", MethodType.methodType(int.class, Object.class, int.class));
            copyBytesOut = lookup.findStatic(cohort, "valueCopyByteArray", MethodType.methodType(byte[].class, Object.class));
            prepare = lookup.findStatic(cohort, "valuePrepareArgument", MethodType.methodType(Object.class, Object.class, int.class, Object.class, String.class));
        } catch (ReflectiveOperationException failure) {
            throw new IllegalStateException("Typed storage protocol is unavailable in this cohort", failure);
        }
    }
    static LeanType.Registry compileTrusted(Class<?> interpreter, Map<String,Object> logical, Map<String,Object> normalized) {
        ValueBridge bridge = BUNDLES.get(interpreter);
        try {
            Object schema = (Object) bridge.compile.invokeExact(logical, normalized);
            @SuppressWarnings("unchecked") Map<String,Object> metadata = (Map<String,Object>) bridge.describe.invokeExact(schema);
            return new LeanType.Registry(bridge, schema, metadata);
        } catch (Throwable failure) { throw failure(failure); }
    }
    static LeanBytes copyBytes(byte[] source) {
        Objects.requireNonNull(source, "source");
        try {
            Class<?> interpreter = Class.forName("ansatz.lean.jvm.internal.exec.Interpreter", true, ValueBridge.class.getClassLoader());
            ValueBridge bridge = BUNDLES.get(interpreter);
            return new LeanBytes(bridge, (Object) bridge.copyBytes.invokeExact(source));
        } catch (Throwable failure) { throw failure(failure); }
    }
    Object freezeBorrowed(LeanType type, Object raw, String lane) {
        try { return (Object) freeze.invokeExact(type.registry.schema, type.plan, raw, lane); }
        catch (Throwable failure) { throw failure(failure); }
    }
    Object prepareArgument(LeanType type, Object capability, String lane) {
        try { return (Object) prepare.invokeExact(type.registry.schema, type.plan, capability, lane); }
        catch (Throwable failure) { throw failure(failure); }
    }
    Object child(Object cap, int index) {
        try { return (Object) child.invokeExact(cap, index); } catch (Throwable failure) { throw failure(failure); }
    }
    int constructorIndex(Object cap) {
        try { return (int) constructorIndex.invokeExact(cap); } catch (Throwable failure) { throw failure(failure); }
    }
    int size(Object cap) {
        try { return (int) size.invokeExact(cap); } catch (Throwable failure) { throw failure(failure); }
    }
    Object scalar(Object cap) {
        try { return (Object) scalar.invokeExact(cap); } catch (Throwable failure) { throw failure(failure); }
    }
    int byteAt(Object cap, int index) {
        try { return (int) byteAt.invokeExact(cap, index); } catch (Throwable failure) { throw failure(failure); }
    }
    byte[] copyBytesOut(Object cap) {
        try { return (byte[]) copyBytesOut.invokeExact(cap); } catch (Throwable failure) { throw failure(failure); }
    }
    private static RuntimeException failure(Throwable failure) {
        if (failure instanceof Error error) throw error;
        if (failure instanceof RuntimeException runtime) return runtime;
        return new IllegalStateException("Typed storage bridge failure", failure);
    }
    @SuppressWarnings("unchecked") static Map<String,Object> map(Object value) { return (Map<String,Object>) value; }
    @SuppressWarnings("unchecked") static List<Object> list(Object value) { return (List<Object>) value; }
    static int integer(Object value) { return ((Number) value).intValue(); }
    private static void require(boolean condition, String message) {
        if (!condition) throw new IllegalArgumentException(message);
    }
    private static void poll() {
        if (Thread.currentThread().isInterrupted()) throw new IllegalStateException("Datatype conversion interrupted");
    }
    static Object view(LeanType type, Object cap) {
        ArrayDeque<Integer> wrappers = new ArrayDeque<>();
        Object result;
        while (true) {
            ValueBridge bridge = type.bridge();
            if (type.kind() == LeanType.Kind.OPTION) {
                if (bridge.constructorIndex(cap) == 0) { result = Optional.empty(); break; }
                wrappers.push(0); cap = bridge.child(cap, 0); type = type.arguments().get(0); continue;
            }
            if (type.kind() == LeanType.Kind.SUM || type.kind() == LeanType.Kind.EXCEPT) {
                int branch = bridge.constructorIndex(cap);
                wrappers.push(branch == 0 ? 1 : 2); cap = bridge.child(cap, 0); type = type.arguments().get(branch); continue;
            }
            result = switch (type.kind()) {
                case NOMINAL -> new LeanData(type, cap);
                case BYTES -> new LeanBytes(bridge, cap);
                case ARRAY, LIST -> new Sequence(type, cap);
                case PRODUCT -> new Fields(type, cap, type.constructorAt(0).fields());
                case UNIT -> LeanUnit.INSTANCE;
                default -> bridge.scalar(cap);
            };
            break;
        }
        while (!wrappers.isEmpty()) result = switch (wrappers.pop()) {
            case 0 -> Optional.of(result);
            case 1 -> LeanChoice.left(result);
            default -> LeanChoice.right(result);
        };
        return result;
    }
    static final class Fields extends AbstractList<Object> implements RandomAccess {
        private final LeanType type;
        private final Object cap;
        private final List<LeanType.Field> fields;
        Fields(LeanType type, Object cap, List<LeanType.Field> fields) {
            this.type = type; this.cap = cap; this.fields = fields;
        }
        @Override public int size() { return fields.size(); }
        @Override public Object get(int index) {
            Objects.checkIndex(index, fields.size());
            return view(fields.get(index).type(), type.bridge().child(cap, index));
        }
    }
    static final class Sequence extends AbstractList<Object> {
        private final LeanType type;
        private final Object cap;
        private final int length;
        Sequence(LeanType type, Object cap) { this.type = type; this.cap = cap; length = type.bridge().size(cap); }
        @Override public int size() { return length; }
        @Override public Object get(int index) {
            Objects.checkIndex(index, length);
            Object cursor = cap;
            if (type.kind() == LeanType.Kind.LIST) {
                for (int i = 0; i < index; i++) cursor = type.bridge().child(cursor, 1);
                return view(type.arguments().get(0), type.bridge().child(cursor, 0));
            }
            return view(type.arguments().get(0), type.bridge().child(cap, index));
        }
        @Override public Iterator<Object> iterator() {
            return new Iterator<>() {
                private int index;
                private Object cursor = cap;
                @Override public boolean hasNext() { return index < length; }
                @Override public Object next() {
                    if (!hasNext()) throw new NoSuchElementException();
                    Object child;
                    if (type.kind() == LeanType.Kind.LIST) {
                        child = type.bridge().child(cursor, 0); cursor = type.bridge().child(cursor, 1);
                    } else child = type.bridge().child(cap, index);
                    index++; return view(type.arguments().get(0), child);
                }
            };
        }
    }
    Object construct(LeanType type, Object hostValue) { return view(type, build(type, hostValue, null)); }
    Object constructConstructor(LeanType.Constructor constructor, List<?> fields) {
        Objects.requireNonNull(fields, "fields");
        return view(constructor.type(), build(constructor.type(), fields, constructor));
    }
    private static Object capability(LeanType expected, Object host) {
        if (host instanceof LeanData data) {
            require(expected.equals(data.type()), "Nominal type mismatch");
            require(expected.bridge().cohort == data.type().bridge().cohort, "Storage cohort mismatch");
            return data.capability();
        }
        if (host instanceof LeanBytes bytes) {
            require(expected.kind() == LeanType.Kind.BYTES && expected.bridge().cohort == bytes.bridge().cohort, "Byte storage type/cohort mismatch");
            return bytes.capability();
        }
        if (host instanceof Sequence sequence) {
            require(expected.equals(sequence.type) && expected.bridge().cohort == sequence.type.bridge().cohort, "Sequence type/cohort mismatch");
            return sequence.cap;
        }
        if (host instanceof Fields fields && expected.kind() == LeanType.Kind.PRODUCT) {
            require(expected.equals(fields.type) && expected.bridge().cohort == fields.type.bridge().cohort, "Product type/cohort mismatch");
            return fields.cap;
        }
        return null;
    }
    private static boolean ordinaryList(Object value) {
        if (!(value instanceof List<?>)) return false;
        Class<?> type = value.getClass();
        return type == CLOJURE_VECTOR || type == ArrayList.class || type == java.util.LinkedList.class
                || switch (type.getName()) {
                    case "java.util.Arrays$ArrayList", "java.util.ImmutableCollections$ListN",
                         "java.util.ImmutableCollections$List12", "java.util.ImmutableCollections$SubList",
                         "java.util.Collections$EmptyList", "java.util.Collections$SingletonList",
                         "java.util.Collections$CopiesList" -> true;
                    default -> false;
                };
    }
    private static boolean ordinaryMap(Object value) {
        if (!(value instanceof Map<?,?>)) return false;
        Class<?> type = value.getClass();
        return type == CLOJURE_ARRAY_MAP || type == CLOJURE_HASH_MAP
                || type == java.util.HashMap.class || type == java.util.LinkedHashMap.class
                || switch (type.getName()) {
                    case "java.util.ImmutableCollections$MapN", "java.util.ImmutableCollections$Map1",
                         "java.util.Collections$EmptyMap", "java.util.Collections$SingletonMap" -> true;
                    default -> false;
                };
    }
    private static Object[] snapshot(Object host, int[] slots) {
        if (host != null && host.getClass() == Object[].class) {
            Object[] values = (Object[]) host;
            require(values.length <= MAX_ITEMS - slots[0], "Container exceeds aggregate slot bound");
            slots[0] += values.length; return values.clone();
        }
        require(ordinaryList(host),
                "Expected a standard indexed List/vector or exact Object[]; custom or delegating adapters are unsupported");
        List<?> values = (List<?>) host;
        int length = values.size(); require(length >= 0 && length <= MAX_ITEMS - slots[0], "Container exceeds aggregate slot bound");
        slots[0] += length;
        Object[] result = new Object[length];
        Iterator<?> iterator = values.iterator();
        for (int i = 0; i < length; i++) { poll(); require(iterator.hasNext(), "Container extent changed"); result[i] = iterator.next(); }
        require(!iterator.hasNext() && values.size() == length, "Container extent changed");
        return result;
    }
    private static BigInteger number(Object value) {
        require(value != null && (value.getClass() == BigInteger.class || value.getClass() == Byte.class
                || value.getClass() == Short.class || value.getClass() == Integer.class || value.getClass() == Long.class),
                "Expected an exact integer carrier");
        BigInteger n = value.getClass() == BigInteger.class ? (BigInteger) value : BigInteger.valueOf(((Number) value).longValue());
        require(n.bitLength() <= 4096 && n.abs().bitLength() <= 4096, "Integer exceeds leaf bound"); return n;
    }
    private static String lane(LeanType type) {
        return switch (type.kind()) {
            case BOOL -> "uint8";
            case CHAR -> "uint32";
            case WORD -> "usize";
            case MACHINE_INT -> "uint" + type.bits();
            case FLOAT -> type.bits() == 32 ? "float32" : "float";
            default -> throw new IllegalArgumentException("Not a scalar type");
        };
    }
    private static long scalarBits(LeanType type, Object value) {
        if (type.kind() == LeanType.Kind.BOOL) {
            require(value != null && value.getClass() == Boolean.class, "Bool requires Boolean"); return (Boolean) value ? 1 : 0;
        }
        if (type.kind() == LeanType.Kind.FLOAT) {
            if (type.bits() == 32) {
                require(value != null && value.getClass() == Float.class, "Float32 requires Float");
                return Integer.toUnsignedLong(Float.floatToRawIntBits((Float) value));
            }
            require(value != null && value.getClass() == Double.class, "Float requires Double");
            return Double.doubleToRawLongBits((Double) value);
        }
        BigInteger n = number(value);
        if (type.kind() == LeanType.Kind.CHAR) {
            require(n.signum() >= 0 && n.compareTo(BigInteger.valueOf(0x10ffff)) <= 0
                    && !(n.intValue() >= 0xd800 && n.intValue() <= 0xdfff), "Invalid Unicode scalar");
        } else {
            int bits = type.bits();
            BigInteger bound = BigInteger.ONE.shiftLeft(type.signed() ? bits - 1 : bits);
            require(n.compareTo(type.signed() ? bound.negate() : BigInteger.ZERO) >= 0
                    && n.compareTo(bound.subtract(BigInteger.ONE)) <= 0, "Integer outside machine range");
        }
        int width = type.kind() == LeanType.Kind.CHAR ? 32 : type.bits();
        return n.and(BigInteger.ONE.shiftLeft(width).subtract(BigInteger.ONE)).longValue();
    }
    private static final class Build {
        final LeanType type; final Object host; final LeanType.Constructor forced;
        String kind; int constructor, next; Object[] values; LeanType[] types; Object[] tokens;
        Map<String,Object> leaf; boolean active;
        Build(LeanType type, Object host, LeanType.Constructor forced) { this.type = type; this.host = host; this.forced = forced; }
    }
    private Object build(LeanType type, Object host, LeanType.Constructor forced) {
        ArrayDeque<Build> stack = new ArrayDeque<>(); stack.push(new Build(type, host, forced));
        IdentityHashMap<Object,Boolean> active = new IdentityHashMap<>();
        List<Object> records = new ArrayList<>(); Object root = null; int work = 0; int[] slots = {0};
        IdentityHashMap<Object,Map<LeanType,Object>> memo = new IdentityHashMap<>();
        while (!stack.isEmpty()) {
            poll(); require(stack.size() <= MAX_DEPTH, "Host value exceeds depth bound");
            Build frame = stack.peek();
            if (frame.kind == null) {
                require(++work <= MAX_ITEMS, "Host value exceeds occurrence bound");
                Object cap = frame.forced == null ? capability(frame.type, frame.host) : null;
                Map<LeanType,Object> cached = frame.forced == null ? memo.get(frame.host) : null;
                Object known = cached == null ? null : cached.get(frame.type);
                if (cap != null || known != null) {
                    Object token = cap == null ? known : Map.of("cap", cap); stack.pop();
                    if (stack.isEmpty()) root = token; else { Build parent = stack.peek(); parent.tokens[parent.next - 1] = token; }
                    continue;
                }
                require(frame.host != null, "Null is not a Java Lean value");
                if (frame.host instanceof List<?> || frame.host instanceof Map<?,?> || frame.host.getClass() == Object[].class) {
                    require(active.put(frame.host, Boolean.TRUE) == null, "Cyclic host value"); frame.active = true;
                }
                initialize(frame, slots);
            }
            if (frame.values != null && frame.next < frame.values.length) {
                int index = frame.next++; stack.push(new Build(frame.types[index], frame.values[index], null)); continue;
            }
            Object token;
            if (frame.kind.equals("list")) {
                int nil = add(records, Map.of("kind", "constructor", "plan", frame.type.plan, "constructor", 0, "fields", List.of()));
                token = Map.of("ref", nil);
                for (int i = frame.tokens.length - 1; i >= 0; i--)
                    token = Map.of("ref", add(records, Map.of("kind", "constructor", "plan", frame.type.plan,
                            "constructor", 1, "fields", List.of(frame.tokens[i], token))));
            } else {
                Map<String,Object> record = frame.leaf;
                if (record == null) record = frame.kind.equals("array")
                        ? Map.of("kind", "array", "plan", frame.type.plan, "elements", List.of(frame.tokens))
                        : Map.of("kind", "constructor", "plan", frame.type.plan, "constructor", frame.constructor, "fields", List.of(frame.tokens));
                token = Map.of("ref", add(records, record));
            }
            if (frame.active) {
                active.remove(frame.host);
                if (frame.forced == null) memo.computeIfAbsent(frame.host, ignored -> new java.util.HashMap<>()).put(frame.type, token);
            }
            stack.pop();
            if (stack.isEmpty()) root = token; else { Build parent = stack.peek(); parent.tokens[parent.next - 1] = token; }
        }
        Object tape = Map.of("schema", "lean-jvm-value-build/1", "records", List.copyOf(records), "root", root);
        try { return (Object) construct.invokeExact(type.registry.schema, type.plan, tape); }
        catch (Throwable failure) { throw failure(failure); }
    }
    private static int add(List<Object> records, Map<String,Object> record) {
        require(records.size() < MAX_ITEMS, "Construction tape exceeds record bound"); records.add(record); return records.size() - 1;
    }
    private static void initialize(Build frame, int[] slots) {
        LeanType type = frame.type; Object host = frame.host;
        frame.kind = "leaf";
        switch (type.kind()) {
            case NAT, INT -> {
                BigInteger n = number(host); require(type.kind() != LeanType.Kind.NAT || n.signum() >= 0, "Negative Nat");
                Object value = n.bitLength() <= 63 ? (Object) Long.valueOf(n.longValue()) : n;
                frame.leaf = Map.of("kind", "leaf", "plan", type.plan, "value", value);
            }
            case STRING -> {
                require(host.getClass() == String.class && ((String) host).length() <= 65536, "Expected bounded String");
                frame.leaf = Map.of("kind", "leaf", "plan", type.plan, "value", host);
            }
            case UNIT -> {
                require(host == LeanUnit.INSTANCE, "Unit requires LeanUnit.INSTANCE");
                frame.leaf = Map.of("kind", "unit", "plan", type.plan);
            }
            case BOOL, CHAR, MACHINE_INT, WORD, FLOAT ->
                frame.leaf = Map.of("kind", "scalar", "plan", type.plan, "lane", lane(type), "bits", scalarBits(type, host));
            case BYTES -> {
                require(host.getClass() == byte[].class && ((byte[]) host).length <= 1048576, "Expected bounded byte[]");
                frame.leaf = Map.of("kind", "bytes", "plan", type.plan, "bytes", host);
            }
            case ARRAY, LIST -> {
                frame.kind = type.kind() == LeanType.Kind.ARRAY ? "array" : "list";
                frame.values = snapshot(host, slots); frame.types = new LeanType[frame.values.length];
                java.util.Arrays.fill(frame.types, type.arguments().get(0));
            }
            case OPTION -> {
                require(host.getClass() == Optional.class, "Option requires Optional");
                Optional<?> option = (Optional<?>) host;
                frame.constructor = option.isPresent() ? 1 : 0;
                frame.values = option.isPresent() ? new Object[]{option.orElseThrow()} : new Object[0];
                frame.types = option.isPresent() ? new LeanType[]{type.arguments().get(0)} : new LeanType[0];
            }
            case SUM, EXCEPT -> {
                require(host.getClass() == LeanChoice.class, "Sum/Except requires LeanChoice");
                LeanChoice choice = (LeanChoice) host; frame.constructor = choice.isLeft() ? 0 : 1;
                frame.values = new Object[]{choice.value()}; frame.types = new LeanType[]{type.arguments().get(frame.constructor)};
            }
            case PRODUCT -> {
                frame.constructor = 0; frame.values = snapshot(host, slots);
                require(frame.values.length == 2, "Product requires two fields"); frame.types = type.arguments().toArray(LeanType[]::new);
            }
            case NOMINAL -> {
                LeanType.Constructor constructor = frame.forced;
                Object fields = host;
                if (constructor == null) {
                    require(ordinaryMap(host), "Expected a standard tagged nominal map; custom or comparator adapters are unsupported");
                    Map<?,?> map = (Map<?,?>) host;
                    require(map.size() == 3 && map.containsKey("lean/type") && map.containsKey("lean/constructor")
                            && map.containsKey("lean/fields"), "Invalid nominal map keys");
                    require(type.nominalId().orElseThrow().equals(map.get("lean/type")), "Nominal identity mismatch");
                    require(map.get("lean/constructor") instanceof LeanName, "Expected structured constructor Name");
                    constructor = type.constructor((LeanName) map.get("lean/constructor")); fields = map.get("lean/fields");
                }
                frame.constructor = constructor.index(); frame.values = snapshot(fields, slots);
                require(frame.values.length == constructor.fields().size(), "Wrong constructor arity");
                frame.types = constructor.fields().stream().map(LeanType.Field::type).toArray(LeanType[]::new);
            }
        }
        if (frame.values != null) frame.tokens = new Object[frame.values.length];
    }
    private record Pair(LeanType leftType, Object left, LeanType rightType, Object right) {}
    static boolean equal(LeanType leftType, Object left, LeanType rightType, Object right) {
        ArrayDeque<Pair> pending = new ArrayDeque<>(); pending.push(new Pair(leftType, left, rightType, right));
        int visits = 0;
        while (!pending.isEmpty()) {
            require(++visits <= MAX_ITEMS, "Equality exceeds value bound");
            Pair pair = pending.pop();
            if (!pair.leftType.equals(pair.rightType)) return false;
            LeanType type = pair.leftType; ValueBridge a = type.bridge(), b = pair.rightType.bridge();
            if (type.kind() == LeanType.Kind.BYTES) {
                int n = a.size(pair.left); if (n != b.size(pair.right)) return false;
                for (int i = 0; i < n; i++) if (a.byteAt(pair.left, i) != b.byteAt(pair.right, i)) return false;
            } else if (type.kind() == LeanType.Kind.ARRAY) {
                int n = a.size(pair.left); if (n != b.size(pair.right)) return false;
                LeanType at = type.arguments().get(0), bt = pair.rightType.arguments().get(0);
                for (int i = n - 1; i >= 0; i--) pending.push(new Pair(at, a.child(pair.left, i), bt, b.child(pair.right, i)));
            } else if (!type.alternatives().isEmpty()) {
                int ctor = a.constructorIndex(pair.left); if (ctor != b.constructorIndex(pair.right)) return false;
                List<LeanType.Field> af = type.constructorAt(ctor).fields(), bf = pair.rightType.constructorAt(ctor).fields();
                for (int i = af.size() - 1; i >= 0; i--)
                    pending.push(new Pair(af.get(i).type(), a.child(pair.left, i), bf.get(i).type(), b.child(pair.right, i)));
            } else if (type.kind() != LeanType.Kind.UNIT && !Objects.equals(a.scalar(pair.left), b.scalar(pair.right))) return false;
        }
        return true;
    }
    private static final class Walk {
        final LeanType type; final Object cap;
        List<LeanType.Field> fields; int count, next, hash; LeanType element;
        Object[] values; boolean initialized;
        Walk(LeanType type, Object cap) { this.type = type; this.cap = cap; }
        LeanType childType(int i) { return element == null ? fields.get(i).type() : element; }
    }
    static int hash(LeanType type, Object cap) {
        ArrayDeque<Walk> stack = new ArrayDeque<>(); stack.push(new Walk(type, cap));
        int visits = 0, result = 0;
        while (!stack.isEmpty()) {
            Walk frame = stack.peek();
            if (!frame.initialized) {
                require(++visits <= MAX_ITEMS, "Hash exceeds value bound"); frame.initialized = true;
                ValueBridge bridge = frame.type.bridge();
                if (frame.type.kind() == LeanType.Kind.BYTES) {
                    frame.hash = new LeanBytes(bridge, frame.cap).hashCode();
                } else if (frame.type.kind() == LeanType.Kind.ARRAY) {
                    frame.count = bridge.size(frame.cap); frame.element = frame.type.arguments().get(0); frame.hash = 1;
                } else if (!frame.type.alternatives().isEmpty()) {
                    int ctor = bridge.constructorIndex(frame.cap); frame.fields = frame.type.constructorAt(ctor).fields();
                    frame.count = frame.fields.size(); frame.hash = 31 * frame.type.hashCode() + ctor;
                } else frame.hash = frame.type.kind() == LeanType.Kind.UNIT ? LeanUnit.INSTANCE.hashCode() : Objects.hashCode(bridge.scalar(frame.cap));
            }
            if (frame.next < frame.count) {
                int index = frame.next++;
                stack.push(new Walk(frame.childType(index), frame.type.bridge().child(frame.cap, index))); continue;
            }
            result = frame.hash; stack.pop();
            if (!stack.isEmpty()) { Walk parent = stack.peek(); parent.hash = 31 * parent.hash + result; }
        }
        return result;
    }
    static Object materialize(LeanType type, Object typedValue) {
        Object cap = type.bridge().build(type, typedValue, null);
        ArrayDeque<Walk> stack = new ArrayDeque<>(); stack.push(new Walk(type, cap));
        int visits = 0; Object result = null;
        while (!stack.isEmpty()) {
            poll(); Walk frame = stack.peek(); ValueBridge bridge = frame.type.bridge();
            if (!frame.initialized) {
                require(++visits <= MAX_ITEMS, "Materialization exceeds value bound"); frame.initialized = true;
                switch (frame.type.kind()) {
                    case BYTES -> result = bridge.copyBytesOut(frame.cap);
                    case ARRAY -> {
                        frame.count = bridge.size(frame.cap); frame.element = frame.type.arguments().get(0);
                    }
                    case LIST -> {
                        // Flatten logical list using a linear cursor; no recursive Java calls.
                        int length = bridge.size(frame.cap); List<Object> children = new ArrayList<>(length);
                        Object cursor = frame.cap;
                        for (int i = 0; i < length; i++) { children.add(bridge.child(cursor, 0)); cursor = bridge.child(cursor, 1); }
                        frame.count = length; frame.element = frame.type.arguments().get(0);
                        frame.fields = null; frame.values = children.toArray();
                    }
                    case NOMINAL, PRODUCT, OPTION, SUM, EXCEPT -> {
                        frame.fields = frame.type.constructorAt(bridge.constructorIndex(frame.cap)).fields();
                        frame.count = frame.fields.size();
                    }
                    case UNIT -> result = LeanUnit.INSTANCE;
                    default -> result = bridge.scalar(frame.cap);
                }
                if (frame.values == null) frame.values = new Object[frame.count];
            }
            if (frame.next < frame.count) {
                int index = frame.next++;
                Object child = frame.type.kind() == LeanType.Kind.LIST ? frame.values[index] : bridge.child(frame.cap, index);
                stack.push(new Walk(frame.childType(index), child)); continue;
            }
            switch (frame.type.kind()) {
                case NOMINAL -> result = Map.of("lean/type", frame.type.nominalId().orElseThrow(),
                        "lean/constructor", frame.type.constructorAt(bridge.constructorIndex(frame.cap)).name(),
                        "lean/fields", List.of(frame.values));
                case PRODUCT, ARRAY, LIST -> result = List.of(frame.values);
                case OPTION -> result = frame.count == 0 ? Optional.empty() : Optional.of(frame.values[0]);
                case SUM, EXCEPT -> result = bridge.constructorIndex(frame.cap) == 0
                        ? LeanChoice.left(frame.values[0]) : LeanChoice.right(frame.values[0]);
                default -> { /* scalar/bytes result was read on entry */ }
            }
            stack.pop();
            if (!stack.isEmpty()) { Walk parent = stack.peek(); parent.values[parent.next - 1] = result; }
        }
        return result;
    }
}
