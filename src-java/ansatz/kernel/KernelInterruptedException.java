package ansatz.kernel;

/**
 * Thrown by the kernel's hot loops (isDefEq, whnfCore) when the running thread
 * has been interrupted — cooperative cancellation, mirroring Lean's
 * {@code check_system} interrupt poll. A search harness aborts a runaway kernel
 * call (e.g. deep definitional equality on a hopeless candidate) by interrupting
 * the worker thread; the kernel then unwinds instead of spinning a CPU-bound
 * thread that survives future-cancel. Unchecked so it propagates through the
 * recursive kernel without signature changes; callers that want to treat it as
 * "not equal here" can catch it, but a benchmark/driver should let it abort.
 */
public final class KernelInterruptedException extends RuntimeException {
    public KernelInterruptedException(String message) {
        super(message);
    }
}
