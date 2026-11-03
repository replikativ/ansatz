package ansatz.lean.jvm;

import ansatz.lean.jvm.internal.exec.Interpreter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.CancellationException;
import java.util.function.Function;

/** Private adapter. Only a future authenticated import publisher may construct
 * these plans. A descriptor or a LeanType supplied by an application is not
 * authority to register a binding with a Project. */
final class PureHostCall {
    private final Interpreter.HostExtern descriptor;
    private final List<LeanType> arguments;
    private final LeanType result;
    private final Function<List<Object>, Object> implementation;

    PureHostCall(Interpreter.HostExtern descriptor, List<LeanType> arguments,
                 LeanType result, Function<List<Object>, Object> implementation) {
        this.descriptor = Objects.requireNonNull(descriptor, "descriptor");
        this.arguments = List.copyOf(arguments);
        this.result = Objects.requireNonNull(result, "result");
        this.implementation = Objects.requireNonNull(implementation, "implementation");
        if (arguments.size() != descriptor.paramTypes().length || arguments.size() > 64)
            throw new IllegalArgumentException("Host signature/ABI arity differs");
        String[] lanes = descriptor.paramTypes();
        for (int i = 0; i < lanes.length; i++) lane(arguments.get(i), lanes[i]);
        lane(result, descriptor.resultType());
    }

    private static void lane(LeanType type, String lane) {
        if (!lane.equals("object") && !lane.equals("tobject") && !lane.equals("tagged")
                && !lane.equals(type.row.get("closedIR")))
            throw new IllegalArgumentException("Host logical type/ABI lane differs");
    }

    void complete(Interpreter engine, Interpreter.HostRequest request) {
        // A stale/mismatched plan must not execute user code or fail another
        // pending call. Identity checks precede conversion and its side effects.
        if (request == null || engine.pendingHostRequest() != request || request.descriptor() != descriptor)
            throw new IllegalStateException("Host request does not belong to this binding");
        engine.validateFrozenHostRequest(request);
        try {
            cancelled();
            Object[] raw = request.arguments();
            String[] lanes = descriptor.paramTypes();
            ArrayList<Object> values = new ArrayList<>(raw.length);
            for (int i = 0; i < raw.length; i++) {
                cancelled();
                Object value = raw[i];
                // Requests expose UInt64/USize as unsigned BigInteger while
                // typed raw storage uses the exact 64 bits in a Long.
                if ((lanes[i].equals("uint64") || lanes[i].equals("usize"))
                        && value != null && value.getClass() == BigInteger.class) {
                    BigInteger unsigned = (BigInteger) value;
                    if (unsigned.signum() < 0 || unsigned.bitLength() > 64)
                        throw new IllegalArgumentException("Invalid unsigned host input");
                    value = Long.valueOf(unsigned.longValue());
                }
                values.add(ValueBridge.exportValue(arguments.get(i), value, lanes[i]));
            }
            Object value = implementation.apply(List.copyOf(values));
            cancelled();
            Object reply = ValueBridge.prepareReply(result, value, descriptor.resultType());
            engine.resumeFrozenHost(request, reply);
        } catch (Throwable failure) {
            // failHost preserves the actual pending ownership packet. Never
            // retry user code or guess at cleanup after a partial failure.
            if (engine.pendingHostRequest() == request) engine.failHost(request, failure);
            if (failure instanceof Error error) throw error;
            if (failure instanceof CancellationException cancelled) throw cancelled;
            throw new LeanException("HostFailure", "host", "Pure host implementation failed");
        }
    }

    private static void cancelled() {
        if (Thread.currentThread().isInterrupted())
            throw new CancellationException("Pure host invocation interrupted");
    }
}
