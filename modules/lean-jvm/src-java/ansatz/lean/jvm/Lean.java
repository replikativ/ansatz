package ansatz.lean.jvm;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

/** Lightweight owner of explicitly loaded, compiled JVM projects. */
public final class Lean implements AutoCloseable {
    private final Set<LeanProject> projects = new LinkedHashSet<>();
    private boolean closed;
    private Object services;

    private Lean() { }

    public static Lean open() { return new Lean(); }

    /**
     * Load an artifact whose manifest digest comes from the application's trusted
     * build descriptor. The caller retains ownership of the supplied stream.
     * This path does not invoke a native compiler or discover a Lean installation.
     */
    public synchronized LeanProject loadArtifact(InputStream input, String expectedManifestSHA256) {
        ensureOpen();
        Objects.requireNonNull(input, "input");
        Objects.requireNonNull(expectedManifestSHA256, "expectedManifestSHA256");
        if (!expectedManifestSHA256.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException("Expected a lowercase SHA-256 manifest digest");
        }
        try {
            LeanProject project = new LeanProject(this, Bridge.OPEN.invoke(services(), input, expectedManifestSHA256));
            projects.add(project);
            return project;
        } catch (Throwable failure) {
            throw Bridge.failure(failure);
        }
    }

    /** Load a JAR/classpath resource; this overload closes its own resource stream. */
    public synchronized LeanProject loadArtifact(ClassLoader loader, String resource, String expectedManifestSHA256)
            throws IOException {
        ensureOpen();
        Objects.requireNonNull(loader, "loader");
        Objects.requireNonNull(resource, "resource");
        try (InputStream input = loader.getResourceAsStream(resource)) {
            if (input == null) throw new IOException("Compiled Lean artifact resource is missing: " + resource);
            return loadArtifact(input, expectedManifestSHA256);
        }
    }

    /**
     * Compile trusted local sources with the explicitly supplied native producer
     * bundle/toolchain, then start one JVM project. Native compile-time IO is
     * permitted by this trusted-source profile; it is not a sandbox.
     */
    public synchronized LeanProject loadProject(Path sourceRoot, ProjectOptions options) {
        ensureOpen();
        Objects.requireNonNull(sourceRoot, "sourceRoot");
        Objects.requireNonNull(options, "options");
        try {
            LeanProject project = new LeanProject(this, Bridge.SOURCE.invoke(services(), sourceRoot, options));
            projects.add(project);
            return project;
        } catch (Throwable failure) {
            throw Bridge.failure(failure);
        }
    }

    private Object services() {
        if (services == null) services = Bridge.RUNTIME.invoke();
        return services;
    }

    private void ensureOpen() {
        if (closed) throw new IllegalStateException("Lean is closed");
    }

    synchronized void released(LeanProject project) { projects.remove(project); }

    @Override
    public synchronized void close() {
        if (closed) return;
        ArrayList<LeanProject> children = new ArrayList<>(projects);
        closed = true;
        Throwable first = null;
        for (LeanProject project : children) {
            try { project.close(); }
            catch (Throwable failure) {
                if (first == null) first = failure;
                else if (failure instanceof Error && !(first instanceof Error)) {
                    first = failure;
                } else if ((failure instanceof VirtualMachineError || failure instanceof ThreadDeath)
                        && !(first instanceof VirtualMachineError) && !(first instanceof ThreadDeath)) {
                    first = failure;
                }
            }
        }
        services = null;
        if (first != null) throw Bridge.failure(first);
    }
}
