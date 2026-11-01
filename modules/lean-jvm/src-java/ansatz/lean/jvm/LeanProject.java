package ansatz.lean.jvm;

import java.math.BigInteger;
import java.util.Objects;
import java.util.function.UnaryOperator;

/** One serialized project branch, with handles bound to its exact loaded code. */
public final class LeanProject implements AutoCloseable {
    private final Lean owner;
    private Object token;
    private boolean closed;

    LeanProject(Lean owner, Object token) {
        this.owner = owner;
        this.token = Objects.requireNonNull(token, "issued project");
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
