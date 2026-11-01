package ansatz.lean.jvm;

import clojure.java.api.Clojure;
import clojure.lang.IExceptionInfo;
import clojure.lang.IFn;
import clojure.lang.Keyword;
import java.io.InterruptedIOException;
import java.security.ProviderException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
import java.util.IdentityHashMap;
import java.util.concurrent.CancellationException;

/** Package-private linkage only; does not export runtime tokens or maps. */
final class Bridge {
    static final String NS = "ansatz.lean.jvm.project";
    static final IFn RUNTIME;
    static final IFn OPEN;
    static final IFn SOURCE;
    static final IFn LOOKUP;
    static final IFn INVOKE;
    static final IFn SIGNATURE;
    static final IFn DESCRIPTOR;
    static final IFn ARITY;
    static final IFn CALL;
    static final IFn MAIN;
    static final IFn CLOSE;

    static {
        Clojure.var("clojure.core", "require").invoke(Clojure.read(NS));
        RUNTIME = Clojure.var(NS, "runtime-service!");
        OPEN = Clojure.var(NS, "open-artifact!");
        SOURCE = Clojure.var(NS, "open-project!");
        LOOKUP = Clojure.var(NS, "lookup-function!");
        INVOKE = Clojure.var(NS, "invoke-function!");
        SIGNATURE = Clojure.var(NS, "function-type!");
        DESCRIPTOR = Clojure.var(NS, "function-descriptor!");
        ARITY = Clojure.var(NS, "function-arity!");
        CALL = Clojure.var(NS, "invoke-arguments!");
        MAIN = Clojure.var(NS, "run-main!");
        CLOSE = Clojure.var(NS, "close!");
    }

    private static String bounded(String value, int maximum) {
        if (value == null) return "";
        return value.length() <= maximum ? value : value.substring(0, maximum);
    }

    static RuntimeException failure(Throwable failure) {
        if (failure instanceof LeanException) return (LeanException) failure;
        String code = "RuntimeBoundary";
        Throwable selected = failure;
        Throwable fatal = null;
        boolean interrupted = false;
        boolean cancelled = false;
        IdentityHashMap<Throwable, Boolean> seen = new IdentityHashMap<>();
        for (Throwable cursor = failure; cursor != null && seen.size() < 16 && !seen.containsKey(cursor);
                cursor = cursor.getCause()) {
            seen.put(cursor, Boolean.TRUE);
            if (cursor instanceof Error && fatal == null) fatal = cursor;
            if (cursor instanceof VirtualMachineError || cursor instanceof ThreadDeath) fatal = cursor;
            if (cursor instanceof InterruptedException || cursor instanceof InterruptedIOException) {
                interrupted = true;
                cancelled = true;
                selected = cursor;
                code = "Cancelled";
            } else if (cursor instanceof CancellationException) {
                cancelled = true;
                selected = cursor;
                code = "Cancelled";
            } else if (!cancelled && cursor.getClass().getName().equals(
                    "ansatz.lean.jvm.internal.exec.Interpreter$RuntimeLimitException")) {
                try {
                    Object actual = cursor.getClass().getMethod("code").invoke(cursor);
                    if ("ResourceLimit".equals(actual) || "Cancelled".equals(actual)) {
                        selected = cursor;
                        code = (String) actual;
                        if ("Cancelled".equals(actual)) cancelled = true;
                    }
                } catch (ReflectiveOperationException ignored) {
                    // Failure projection must not retain another reflective cause.
                }
            } else if (!cancelled && (cursor instanceof ProviderException
                    || cursor instanceof NoSuchAlgorithmException || cursor instanceof NoSuchProviderException)) {
                selected = cursor;
                code = cursor instanceof ProviderException ? "ProviderFailure" : "ProviderUnavailable";
            } else if (cursor instanceof IExceptionInfo && "RuntimeBoundary".equals(code)) {
                Object actual = ((IExceptionInfo) cursor).getData().valAt(Keyword.intern("code"));
                if (actual instanceof String && ((String) actual).length() <= 96) {
                    code = (String) actual;
                    selected = cursor;
                }
            } else if ("RuntimeBoundary".equals(code)) {
                // Prefer the useful ordinary cause over a reflection wrapper;
                // only bounded strings are copied to the public exception.
                selected = cursor;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
        // Fatal host Errors follow standard JVM Throwable semantics, including
        // exact identity/class and any cause they themselves retain. Only the
        // ordinary LeanException projection promises bounded value-only data.
        if (fatal != null) throw (Error) fatal;
        String message = selected.getMessage();
        if (message == null) message = selected.getClass().getName();
        // Actual category survives wrappers; original causes/ex-data may retain
        // guest owners, and are deliberately absent from the Java exception.
        return new LeanException(code, bounded(selected.getClass().getName(), 256), bounded(message, 2048));
    }

    private Bridge() { }
}
