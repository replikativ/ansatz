package ansatz.lean.jvm;

import java.math.BigInteger;
import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * One loaded Lean project: its code, initialized globals and serialized calls.
 * A call that fails during execution retires the engine; {@link #restart()}
 * reinitializes it from the same verified artifact.
 */
public final class LeanProject implements AutoCloseable {
    private final Lean owner;
    private Object token;
    private boolean closed;

    LeanProject(Lean owner, Object token) {
        this.owner = owner;
        this.token = Objects.requireNonNull(token, "issued project");
    }

    /** Resolve an exported checked entry without choosing a type-specific API. */
    @SuppressWarnings("unchecked")
    public synchronized LeanFunction function(String name) {
        ensureOpen();
        Object handle = lookup(name, null);
        try {
            String signature = (String) Bridge.SIGNATURE.invoke(token, handle);
            int arity = ((Number) Bridge.ARITY.invoke(token, handle)).intValue();
            java.util.Map<String, Object> descriptor = (java.util.Map<String, Object>) Bridge.DESCRIPTOR.invoke(token, handle);
            java.util.List<?> types = (java.util.List<?>) Bridge.TYPES.invoke(token, handle);
            return new LeanFunction(this, handle, name, signature, arity, descriptor,
                    types == null ? null : (java.util.List<LeanType>) types.get(0),
                    types == null ? null : (LeanType) types.get(1));
        } catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    public synchronized Object call(String name, Object... arguments) {
        return function(name).invoke(arguments);
    }

    public synchronized Object callWith(String name, InvocationOptions options, Object... arguments) {
        return function(name).invokeWith(options, arguments);
    }

    synchronized Object invokeFunction(Object handle, int arity, Object[] arguments) {
        ensureOpen();
        if (arguments == null || arguments.length != arity) {
            throw new LeanException("ArityMismatch", "arguments", "Expected " + arity + " explicit arguments");
        }
        try { return Bridge.CALL.invoke(token, handle, arguments.clone()); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    synchronized Object invokeFunctionWith(Object handle, int arity, InvocationOptions options, Object[] arguments) {
        ensureOpen();
        Objects.requireNonNull(options, "options");
        if (arguments == null || arguments.length != arity)
            throw new LeanException("ArityMismatch", "arguments", "Expected " + arity + " explicit arguments");
        try { return Bridge.CALL_WITH.invoke(token, handle, arguments.clone(), options); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    public synchronized UnaryOperator<BigInteger> natFunction(String name) {
        ensureOpen();
        Object handle = lookup(name, "nat-to-nat");
        return input -> invokeNat(handle, input);
    }

    public synchronized UnaryOperator<String> stringFunction(String name) {
        ensureOpen();
        Object handle = lookup(name, "string-to-string");
        return input -> invokeString(handle, input);
    }

    private Object lookup(String name, String signature) {
        Objects.requireNonNull(name, "name");
        try { return Bridge.LOOKUP.invoke(token, name, signature); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    private synchronized BigInteger invokeNat(Object handle, BigInteger input) {
        ensureOpen();
        Objects.requireNonNull(input, "input");
        if (input.getClass() != BigInteger.class) throw new IllegalArgumentException("Nat input must be an exact BigInteger");
        if (input.signum() < 0) throw new IllegalArgumentException("Nat input must be nonnegative");
        try { return (BigInteger) Bridge.INVOKE.invoke(token, handle, input); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    private synchronized String invokeString(Object handle, String input) {
        ensureOpen();
        Objects.requireNonNull(input, "input");
        if (input.length() > 65536) throw new IllegalArgumentException("String input exceeds 65536 UTF-16 units");
        for (int i = 0; i < input.length(); i++) {
            char c = input.charAt(i);
            if (Character.isHighSurrogate(c)) {
                if (++i >= input.length() || !Character.isLowSurrogate(input.charAt(i))) {
                    throw new IllegalArgumentException("String input must be valid UTF-16");
                }
            } else if (Character.isLowSurrogate(c)) {
                throw new IllegalArgumentException("String input must be valid UTF-16");
            }
        }
        try { return (String) Bridge.INVOKE.invoke(token, handle, input); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    /**
     * True after a call failed during execution (for example by exceeding its
     * budget, or reaching {@code panic!} with the fail-on-panic policy). Later
     * calls are refused with {@code ProjectFailed} until {@link #restart()}.
     */
    public synchronized boolean isFailed() {
        ensureOpen();
        try { return "failed".equals(Bridge.STATUS.invoke(token)); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    /**
     * Discard this Project's engine and initialize a fresh one from the same
     * verified artifact, without re-reading or re-verifying it. Existing
     * {@link LeanFunction} handles stay valid. Module initializers run again, so
     * globals and {@code IO.Ref} state start over.
     */
    public synchronized void restart() {
        ensureOpen();
        try { Bridge.RESTART.invoke(token); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    public synchronized MainResult runMain() {
        ensureOpen();
        try { return (MainResult) Bridge.MAIN.invoke(token); }
        catch (Throwable failure) { throw Bridge.failure(failure); }
    }

    private void ensureOpen() {
        if (closed) throw new IllegalStateException("LeanProject is closed");
    }

    @Override
    public void close() {
        try {
            synchronized (this) {
                if (closed) return;
                closed = true;
                try { Bridge.CLOSE.invoke(token); }
                catch (Throwable failure) { throw Bridge.failure(failure); }
                finally { token = null; }
            }
        } finally {
            owner.released(this);
        }
    }
}
