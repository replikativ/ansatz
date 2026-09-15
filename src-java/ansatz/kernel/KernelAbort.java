package ansatz.kernel;

/**
 * Thrown when a check must stop for a reason that is not a type error: the checking thread
 * was interrupted (a timeout) or the fuel budget is spent. Lean's kernel has `check_system`
 * for the first; here the kernel's few catch-alls (eta for structures, unit-like types, proof
 * irrelevance) let this pass, so a timed-out check ends instead of continuing as "unknown".
 */
public final class KernelAbort extends RuntimeException {
    public KernelAbort(String message) { super(message); }
}
