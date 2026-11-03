package ansatz.lean.jvm;

/** A checked exported function, bound to one loaded Project's lifetime. */
public final class LeanFunction {
    private final LeanProject owner;
    private final Object handle;
    private final String name;
    private final String signature;
    private final int arity;
    private final java.util.Map<String, Object> descriptor;
    private final java.util.List<LeanType> argumentTypes;
    private final LeanType resultType;

    LeanFunction(LeanProject owner, Object handle, String name, String signature, int arity,
                 java.util.Map<String, Object> descriptor,
                 java.util.List<LeanType> argumentTypes, LeanType resultType) {
        this.owner = owner;
        this.handle = handle;
        this.name = name;
        this.signature = signature;
        this.arity = arity;
        this.descriptor = java.util.Map.copyOf(descriptor);
        this.argumentTypes = argumentTypes == null ? null : java.util.List.copyOf(argumentTypes);
        this.resultType = resultType;
    }

    public String name() { return name; }
    /** The native-checked calling profile; this is not inferred from erased IR. */
    public String signature() { return signature; }
    /** Explicit host arguments; an IO world argument is supplied internally. */
    public int arity() { return arity; }
    /** Immutable closed calling descriptor, without source or interpreter owners. */
    public java.util.Map<String, Object> descriptor() { return descriptor; }
    /** V3 prepared projects expose detached native-derived construction types. */
    public boolean hasTypeMetadata() { return resultType != null; }
    public java.util.List<LeanType> argumentTypes() {
        if (!hasTypeMetadata()) throw new LeanException("UnsupportedSignature", "types", "Reprepare with the v3 producer for detached type metadata");
        return argumentTypes;
    }
    public LeanType resultType() {
        if (!hasTypeMetadata()) throw new LeanException("UnsupportedSignature", "types", "Reprepare with the v3 producer for detached type metadata");
        return resultType;
    }

    /** Unsupported argument types/arities fail before guest execution. */
    public Object invoke(Object... arguments) {
        return owner.invokeFunction(handle, arity, arguments);
    }

    /** Supply finite stdin and tighter output limits for this invocation. */
    public Object invokeWith(InvocationOptions options, Object... arguments) {
        return owner.invokeFunctionWith(handle, arity, java.util.Objects.requireNonNull(options, "options"), arguments);
    }
}
