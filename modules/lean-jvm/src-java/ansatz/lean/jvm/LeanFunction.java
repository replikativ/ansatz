package ansatz.lean.jvm;

/** A checked exported function, bound to one loaded Project's lifetime. */
public final class LeanFunction {
    private final LeanProject owner;
    private final Object handle;
    private final String name;
    private final String signature;
    private final int arity;
    private final java.util.Map<String, Object> descriptor;

    LeanFunction(LeanProject owner, Object handle, String name, String signature, int arity,
                 java.util.Map<String, Object> descriptor) {
        this.owner = owner;
        this.handle = handle;
        this.name = name;
        this.signature = signature;
        this.arity = arity;
        this.descriptor = java.util.Map.copyOf(descriptor);
    }

    public String name() { return name; }
    /** The native-checked calling profile; this is not inferred from erased IR. */
    public String signature() { return signature; }
    /** Explicit host arguments; an IO world argument is supplied internally. */
    public int arity() { return arity; }
    /** Immutable closed calling descriptor, without source or interpreter owners. */
    public java.util.Map<String, Object> descriptor() { return descriptor; }

    /** Unsupported argument types/arities fail before guest execution. */
    public Object invoke(Object... arguments) {
        return owner.invokeFunction(handle, arity, arguments);
    }
}
