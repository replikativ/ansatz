package ansatz.lean;

import clojure.java.api.Clojure;
import clojure.lang.*;
import ansatz.kernel.Name;
import java.math.BigInteger;
import java.nio.file.Path;
import java.util.*;

/** Provider-first experimental facade. DTO bytecode targets 11; runtime requires JDK 17+. */
public final class LeanRuntime {
    private LeanRuntime() {}
    private static Keyword kw(String name) { return Keyword.intern(null, name); }
    private static final IFn REQUIRE = Clojure.var("clojure.core", "require");
    static { REQUIRE.invoke(Clojure.read("ansatz.lean")); }
    private static IFn fn(String name) { return Clojure.var("ansatz.lean", name); }
    private static Object get(Object map, String key) { return ((ILookup) map).valAt(kw(key)); }
    private static IPersistentMap map(Object... pairs) { return PersistentArrayMap.createAsIfByAssoc(pairs); }
    private static <T> List<T> copy(List<T> values) {
        return Collections.unmodifiableList(new ArrayList<>(Objects.requireNonNull(values)));
    }
    private static Object invoke(String operation, Object... args) {
        try { return fn(operation).applyTo(RT.seq(args)); }
        catch (RuntimeException cause) { throw new LeanException(operation, cause); }
    }

    /** Trusted provider must keep its borrowed source lease open through all users and failures. */
    @FunctionalInterface public interface PreparedProvider { PreparedInput prepare(OpenOptions options) throws Exception; }
    @FunctionalInterface public interface HostFunction { Object apply(List<?> immutableArguments) throws Exception; }

    /** Opaque adapter packet; possession does not bypass open-checked live admission. */
    public static final class PreparedInput {
        private final Object candidate, configuration, sourceLease;
        public PreparedInput(Object candidate, Object independentConfiguration, Object borrowedSourceLease) {
            this.candidate = Objects.requireNonNull(candidate);
            this.configuration = Objects.requireNonNull(independentConfiguration);
            this.sourceLease = Objects.requireNonNull(borrowedSourceLease);
        }
    }
    public static final class OpenOptions {
        private final Map<String, Object> values;
        public OpenOptions(Map<String, Object> values) {
            this.values = Collections.unmodifiableMap(new LinkedHashMap<>(values));
        }
        public Map<String, Object> values() { return values; }
    }
    public static LeanContext open(PreparedProvider provider, OpenOptions options) {
        Objects.requireNonNull(provider); Objects.requireNonNull(options);
        IFn acquire = new AFn() {
            @Override public Object invoke(Object ignored) {
                try {
                    PreparedInput input = Objects.requireNonNull(provider.prepare(options));
                    return map(kw("candidate"), input.candidate, kw("configuration"), input.configuration,
                               kw("source-lease"), input.sourceLease);
                } catch (Exception failure) { throw new RuntimeException("Prepared provider failed", failure); }
            }
        };
        return new LeanContext(invoke("open", map(kw("provider"), acquire, kw("options"), options)));
    }
    /** Dotted strings always use string segments; use structuredName for numeric/literal-dot segments. */
    public static Name name(String dotted) { return (Name) invoke("name", dotted); }
    public static Name structuredName(List<?> segments) { return (Name) invoke("name", PersistentVector.create(segments)); }

    public enum Initialization { DEFER, RUN }
    public static final class SourceRequest {
        private final Name module;
        private final List<Name> roots;
        private final Initialization initialization;
        private final String fileName;
        public SourceRequest(Name module, List<Name> roots, Initialization initialization, String fileName) {
            this.module = Objects.requireNonNull(module); this.roots = copy(roots);
            this.initialization = Objects.requireNonNull(initialization); this.fileName = Objects.requireNonNull(fileName);
        }
        private Object data() {
            return map(kw("module"), module, kw("roots"), PersistentVector.create(roots),
                       kw("initialization"), kw(initialization == Initialization.DEFER ? "defer" : "run"),
                       kw("file-name"), fileName);
        }
    }
    /** Descriptor is a codec keyword/string, or a recursive List such as ["option", "nat"]. */
    private static Object descriptor(Object value) {
        if (value instanceof String) return kw((String) value);
        if (value instanceof List) {
            List<Object> children = new ArrayList<>();
            for (Object child : (List<?>) value) children.add(descriptor(child));
            return PersistentVector.create(children);
        }
        return value;
    }
    public static final class CallSignature {
        private final List<?> arguments;
        private final Object result;
        public CallSignature(List<?> arguments, Object result) {
            List<Object> codecs = new ArrayList<>();
            for (Object codec : arguments) codecs.add(descriptor(codec));
            this.arguments = copy(codecs); this.result = descriptor(result);
        }
        private Object data() {
            return map(kw("arguments"), PersistentVector.create(arguments), kw("result"), result);
        }
    }
    /** Exact boxed ABI parameter; ownership must match the declaration's borrow bit. */
    public static final class ExternArgument {
        private final String type, codec;
        private final boolean borrowed;
        public ExternArgument(String type, boolean borrowed, String codec) {
            this.type = Objects.requireNonNull(type); this.borrowed = borrowed;
            if (!"nat".equals(codec) && !"string".equals(codec)) throw new IllegalArgumentException("Nat/String extern codec required");
            this.codec = codec;
        }
    }
    public static final class ExternSpec {
        private final String symbol, returnType, result;
        private final List<ExternArgument> arguments;
        private final HostFunction function;
        public ExternSpec(String symbol, List<ExternArgument> arguments, String returnType, String result, HostFunction function) {
            this.symbol = Objects.requireNonNull(symbol); this.arguments = copy(arguments);
            this.returnType = Objects.requireNonNull(returnType); this.result = Objects.requireNonNull(result);
            this.function = Objects.requireNonNull(function);
            if (!"nat".equals(result) && !"string".equals(result)) throw new IllegalArgumentException("Nat/String extern result required");
        }
        private Object data() {
            List<Object> params = new ArrayList<>(), codecs = new ArrayList<>();
            for (ExternArgument argument : arguments) {
                params.add(map(kw("ty"), argument.type, kw("borrow"), argument.borrowed));
                codecs.add(map(kw("codec"), kw(argument.codec), kw("ownership"), kw(argument.borrowed ? "borrowed" : "owned")));
            }
            IFn host = new AFunction() {
                @Override public Object applyTo(ISeq args) {
                    List<Object> decoded = new ArrayList<>(); int i = 0;
                    for (ISeq cursor = args; cursor != null; cursor = cursor.next()) {
                        decoded.add(javaValue(kw(arguments.get(i++).codec), cursor.first()));
                    }
                    try { return function.apply(Collections.unmodifiableList(decoded)); }
                    catch (Exception failure) { throw new RuntimeException("Host callback failed", failure); }
                }
            };
            return map(kw("symbol"), symbol, kw("signature"), map(kw("params"), PersistentVector.create(params), kw("return-type"), returnType),
                       kw("arguments"), PersistentVector.create(codecs), kw("result"), kw(result), kw("fn"), host);
        }
    }
    private static Object javaValue(Object codec, Object value) {
        if (kw("nat").equals(codec)) {
            if (value instanceof BigInteger) return value;
            if (value instanceof BigInt) return ((BigInt) value).toBigInteger();
            return BigInteger.valueOf(((Number) value).longValue());
        }
        if (codec instanceof IPersistentVector && kw("option").equals(((IPersistentVector) codec).nth(0)) && value != null) {
            return Collections.singletonMap("some", javaValue(((IPersistentVector) codec).nth(1), get(value, "some")));
        }
        return value;
    }
    private static Object guestValue(Object codec, Object value) {
        // Preserve exact unsigned element values; the existing codec validates 0..255.
        if (kw("bytes").equals(codec) && value instanceof List) return PersistentVector.create((List<?>) value);
        if (codec instanceof IPersistentVector && kw("option").equals(((IPersistentVector) codec).nth(0)) && value != null) {
            if (!(value instanceof Map) || !((Map<?, ?>) value).containsKey("some") || ((Map<?, ?>) value).size() != 1)
                throw new IllegalArgumentException("Option requires null or a single some entry");
            return map(kw("some"), guestValue(((IPersistentVector) codec).nth(1), ((Map<?, ?>) value).get("some")));
        }
        return value;
    }
    public static final class LeanFile {
        private final Object handle;
        private LeanFile(Object handle) { this.handle = handle; }
    }
    public static final class CapturedSource {
        private final Object data;
        private CapturedSource(Object data) { this.data = data; }
        public String text() { return (String) get(data, "text"); }
        public String sha256() { return (String) get(data, "sha256"); }
        public String fileName() { return (String) get(data, "file-name"); }
        public Name module() { return (Name) get(data, "module"); }
    }
    public static final class LoadResult {
        private final LeanContext context;
        private final LeanFile file;
        private final boolean success;
        private final Object diagnostics;
        private final CapturedSource source;
        private LoadResult(Object data) {
            context = new LeanContext(get(data, "context")); Object handle = get(data, "file");
            file = handle == null ? null : new LeanFile(handle); success = Boolean.TRUE.equals(get(data, "success?"));
            diagnostics = get(data, "diagnostics"); source = new CapturedSource(get(data, "source"));
        }
        public LeanContext context() { return context; }
        public LeanFile file() { return file; }
        public boolean success() { return success; }
        /** Original immutable diagnostic records; no invented span convention. */
        public Object diagnostics() { return diagnostics; }
        public CapturedSource source() { return source; }
    }
    public static final class CallResult {
        private final LeanContext context;
        private final Object value;
        private CallResult(Object data, Object codec) {
            context = new LeanContext(get(data, "context")); value = javaValue(codec, get(data, "value"));
        }
        public LeanContext context() { return context; }
        public Object value() { return value; }
    }
    public static final class LeanContext implements AutoCloseable {
        private final Object handle;
        private LeanContext(Object handle) { this.handle = handle; }
        public LeanContext fork() { return new LeanContext(invoke("fork", handle)); }
        public LoadResult loadFile(Path path, SourceRequest request) {
            return new LoadResult(invoke("load-file", handle, path, request.data()));
        }
        public LoadResult loadString(String text, SourceRequest request) {
            return new LoadResult(invoke("load-string", handle, text, request.data()));
        }
        public LeanContext initialize(LeanFile file) { return new LeanContext(invoke("initialize", handle, file.handle)); }
        public CallResult call(LeanFile file, Name name, List<?> arguments, CallSignature signature) {
            List<Object> encoded = new ArrayList<>();
            if (arguments.size() != signature.arguments.size()) throw new IllegalArgumentException("Argument/codec arity mismatch");
            for (int i = 0; i < arguments.size(); i++) encoded.add(guestValue(signature.arguments.get(i), arguments.get(i)));
            return new CallResult(invoke("call", handle, file.handle, name, PersistentVector.create(encoded), signature.data()), signature.result);
        }
        public CallResult call(LeanFile file, String name, List<?> arguments, CallSignature signature) {
            return call(file, LeanRuntime.name(name), arguments, signature);
        }
        public LeanContext withExterns(List<ExternSpec> externs) {
            IPersistentMap bindings = PersistentArrayMap.EMPTY;
            for (ExternSpec extern : externs) {
                IPersistentMap binding = (IPersistentMap) invoke("extern", extern.data());
                if (bindings.containsKey(extern.symbol)) throw new IllegalArgumentException("Duplicate extern symbol");
                bindings = bindings.assoc(extern.symbol, binding.valAt(extern.symbol));
            }
            return new LeanContext(invoke("with-externs", handle, bindings));
        }
        @Override public void close() { invoke("close!", handle); }
    }
    /** Original Clojure cause retains exact checkpoint/owner evidence. Never replay effects. */
    public static final class LeanException extends RuntimeException {
        private final String operation;
        private LeanException(String operation, RuntimeException cause) { super("Lean " + operation + " failed", cause); this.operation = operation; }
        public String operation() { return operation; }
        public Object failure() {
            Throwable cause = getCause();
            return cause instanceof IExceptionInfo ? ((IExceptionInfo) cause).getData().valAt(Keyword.intern("lean", "failure")) : null;
        }
    }
}
