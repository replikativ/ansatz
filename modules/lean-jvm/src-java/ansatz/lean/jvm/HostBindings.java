package ansatz.lean.jvm;

import clojure.lang.IFn;
import clojure.lang.Var;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/** Explicit host implementation choices. Signatures come from authenticated
 * Lean declarations. Pure bindings promise stable results; reference replacements
 * additionally promise equivalence to the Lean body. */
public final class HostBindings {
    public static final int MAX_BINDINGS = 1024;
    private static final HostBindings EMPTY = new HostBindings(List.of());

    /** Detached signature supplied once to an implementation factory. */
    public static final class Signature {
        private final List<LeanType> arguments;
        private final LeanType result;
        public Signature(List<LeanType> arguments, LeanType result) {
            this.arguments = List.copyOf(arguments); this.result = Objects.requireNonNull(result, "result");
            if (arguments.size() > 64) throw new IllegalArgumentException("Host signature arity exceeds profile");
        }
        public List<LeanType> argumentTypes() { return arguments; }
        public LeanType resultType() { return result; }
    }

    public static final class Entry {
        private final String name, implementationId;
        private final Object implementation;
        private final boolean clojure, factory, io;
        private Entry(String name, String implementationId, Object implementation, boolean clojure, boolean factory, boolean io) {
            this.name = name; this.implementationId = implementationId;
            this.implementation = implementation; this.clojure = clojure; this.factory = factory; this.io = io;
        }
        public String name() { return name; }
        /** Diagnostic/version label, not a proof of purity or code identity. */
        public String implementationId() { return implementationId; }
        public boolean isClojure() { return clojure; }
        public boolean isFactory() { return factory; }
        public boolean isIO() { return io; }
        /** The host's own captured callable, never a guest runtime object. */
        public Object implementation() { return implementation; }
    }
    public static final class Builder {
        private final LinkedHashMap<String, Entry> entries = new LinkedHashMap<>();
        private Builder() {}
        public Builder pure(String name, String implementationId, Function<List<Object>, Object> implementation) {
            return add(name, implementationId, Objects.requireNonNull(implementation, "implementation"), false, false, false);
        }
        /** Derive nominal constructors from the Lean signature once at linking. */
        public Builder pureFactory(String name, String implementationId,
                Function<Signature, Function<List<Object>, Object>> factory) {
            return add(name, implementationId, Objects.requireNonNull(factory, "factory"), false, true, false);
        }
        /** Capture the current IFn target once, including when given a Var.
         * Dependencies, dynamic state and mutable captures are not frozen. */
        public Builder pureClojure(String name, String implementationId, IFn implementation) {
            return captureClojure(name, implementationId, implementation, false, false);
        }
        public Builder pureClojureFactory(String name, String implementationId, IFn factory) {
            return captureClojure(name, implementationId, factory, true, false);
        }
        /** Synchronous IO implementation. Throw LeanIOError for a catchable Lean error. */
        public Builder io(String name, String implementationId, Function<List<Object>, Object> implementation) {
            return add(name, implementationId, Objects.requireNonNull(implementation, "implementation"), false, false, true);
        }
        public Builder ioFactory(String name, String implementationId,
                Function<Signature, Function<List<Object>, Object>> factory) {
            return add(name, implementationId, Objects.requireNonNull(factory, "factory"), false, true, true);
        }
        public Builder ioClojure(String name, String implementationId, IFn implementation) {
            return captureClojure(name, implementationId, implementation, false, true);
        }
        public Builder ioClojureFactory(String name, String implementationId, IFn factory) {
            return captureClojure(name, implementationId, factory, true, true);
        }
        private Builder captureClojure(String name, String implementationId, IFn implementation, boolean factory, boolean io) {
            Objects.requireNonNull(implementation, "implementation");
            Object target = implementation;
            if (implementation instanceof Var var) {
                if (!var.isBound()) throw new IllegalArgumentException("Unbound implementation Var");
                target = var.deref();
            }
            if (!(target instanceof IFn)) throw new IllegalArgumentException("Expected an actual Clojure function");
            return add(name, implementationId, target, true, factory, io);
        }
        private Builder add(String name, String implementationId, Object implementation, boolean clojure, boolean factory, boolean io) {
            Objects.requireNonNull(name, "name"); Objects.requireNonNull(implementationId, "implementationId");
            if (name.isEmpty() || name.length() > 4096 || name.indexOf('\0') >= 0
                    || implementationId.isEmpty() || implementationId.length() > 256 || implementationId.indexOf('\0') >= 0)
                throw new IllegalArgumentException("Bounded declaration name and implementation ID required");
            if (entries.size() >= MAX_BINDINGS || entries.containsKey(name))
                throw new IllegalArgumentException("Host bindings must be distinct and bounded");
            entries.put(name, new Entry(name, implementationId, implementation, clojure, factory, io));
            return this;
        }
        public HostBindings build() { return entries.isEmpty() ? EMPTY : new HostBindings(List.copyOf(entries.values())); }
    }
    private final List<Entry> entries;
    private HostBindings(List<Entry> entries) { this.entries = entries; }
    public static HostBindings empty() { return EMPTY; }
    public static Builder builder() { return new Builder(); }
    public List<Entry> entries() { return entries; }
}
