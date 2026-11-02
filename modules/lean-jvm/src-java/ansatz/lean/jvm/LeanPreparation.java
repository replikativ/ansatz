package ansatz.lean.jvm;

import clojure.lang.ILookup;
import clojure.lang.Keyword;
import java.io.OutputStream;
import java.nio.file.Path;
import java.util.Objects;

/** Trusted native source preparation, separate from JVM project execution. */
public final class LeanPreparation {
    private LeanPreparation() { }

    /**
     * Compile and export checked source evidence without creating a JVM Project
     * or invoking its initializers/main. The native frontend is trusted and can
     * run compile-time metaprograms and IO. The caller retains OUTPUT ownership,
     * including on failure; failed writes can leave partial bytes in that stream.
     * This method does not choose or install a native toolchain/producer bundle.
     */
    public static PreparedArtifact prepareProject(Path sourceRoot, ProjectOptions options, OutputStream output) {
        Objects.requireNonNull(sourceRoot, "sourceRoot");
        Objects.requireNonNull(options, "options");
        Objects.requireNonNull(output, "output");
        try {
            ILookup result = (ILookup) Bridge.Preparation.PREPARE.invoke(sourceRoot, options, output);
            return new PreparedArtifact((String) result.valAt(Keyword.intern("manifest-sha256")),
                                        (String) result.valAt(Keyword.intern("archive-sha256")));
        } catch (Throwable failure) {
            throw Bridge.Failure.project(failure);
        }
    }

    /** Command-line producer. Only this process entry point may terminate the JVM. */
    public static void main(String[] arguments) {
        int status;
        try {
            status = ((Number) Bridge.Preparation.CLI.invoke(arguments)).intValue();
        } catch (Throwable failure) {
            RuntimeException projected = Bridge.Failure.project(failure);
            System.err.println("PreparationFailed: " + projected.getMessage());
            status = 2;
        } finally {
            clojure.java.api.Clojure.var("clojure.core", "shutdown-agents").invoke();
        }
        if (status != 0) System.exit(status);
    }
}
