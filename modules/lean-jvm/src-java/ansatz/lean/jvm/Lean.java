package ansatz.lean.jvm;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

/**
 * Lightweight owner of explicitly loaded, compiled JVM projects. Loads run
 * concurrently; each Project serializes its own calls.
 */
public final class Lean implements AutoCloseable {
    private final Set<LeanProject> projects = new LinkedHashSet<>();
    private final HostServices hostServices;
    private boolean closed;
    private Object services;

    private Lean() { hostServices = null; }
    private Lean(HostServices services) { hostServices = Objects.requireNonNull(services, "services"); }

    public static Lean open() { return new Lean(); }
    /** Capture immutable explicit runtime services; acquisition remains lazy. */
    public static Lean open(HostServices services) { return new Lean(services); }

    /**
     * Load an artifact whose manifest digest comes from the application's trusted
     * build descriptor. The caller retains ownership of the supplied stream.
     * This path does not invoke a native compiler or discover a Lean installation.
     */
    public LeanProject loadArtifact(InputStream input, String expectedManifestSHA256) {
        return loadArtifact(input, expectedManifestSHA256, HostBindings.empty());
    }

    /** Select pure or IO implementations against the artifact's checked binding evidence. */
    public LeanProject loadArtifact(InputStream input, String expectedManifestSHA256, HostBindings bindings) {
        Objects.requireNonNull(input, "input");
        Objects.requireNonNull(expectedManifestSHA256, "expectedManifestSHA256");
        Objects.requireNonNull(bindings, "bindings");
        if (!expectedManifestSHA256.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException("Expected a lowercase SHA-256 manifest digest");
        }
        Object scope = openServices();
        Object token;
        try {
            token = Bridge.OPEN.invoke(scope, input, expectedManifestSHA256, bindings);
        } catch (Throwable failure) {
            throw Bridge.failure(failure);
        }
        return adopt(token);
    }

    /** Load a JAR/classpath resource; this overload closes its own resource stream. */
    public LeanProject loadArtifact(ClassLoader loader, String resource, String expectedManifestSHA256)
            throws IOException {
        return loadArtifact(loader, resource, expectedManifestSHA256, HostBindings.empty());
    }

    public LeanProject loadArtifact(ClassLoader loader, String resource, String expectedManifestSHA256,
                                    HostBindings bindings) throws IOException {
        synchronized (this) { ensureOpen(); }
        Objects.requireNonNull(loader, "loader");
        Objects.requireNonNull(resource, "resource");
        try (InputStream input = loader.getResourceAsStream(resource)) {
            if (input == null) throw new IOException("Compiled Lean artifact resource is missing: " + resource);
            return loadArtifact(input, expectedManifestSHA256, bindings);
        }
    }

    /**
     * Compile trusted local sources with the explicitly supplied native producer
     * bundle/toolchain, then start one JVM project. Native compile-time IO is
     * permitted by this trusted-source profile; it is not a sandbox.
     */
    public LeanProject loadProject(Path sourceRoot, ProjectOptions options) {
        return loadProject(sourceRoot, options, HostBindings.empty());
    }

    /** Bindings supply required foreign imports or replace eligible noinline reference definitions. */
    public LeanProject loadProject(Path sourceRoot, ProjectOptions options, HostBindings bindings) {
        Objects.requireNonNull(sourceRoot, "sourceRoot");
        Objects.requireNonNull(options, "options");
        Objects.requireNonNull(bindings, "bindings");
        Object scope = openServices();
        Object token;
        try {
            token = Bridge.SOURCE.invoke(scope, sourceRoot, options, bindings);
        } catch (Throwable failure) {
            throw Bridge.failure(failure);
        }
        return adopt(token);
    }

    private synchronized Object openServices() {
        ensureOpen();
        try {
            if (services == null) services = hostServices == null ? Bridge.RUNTIME.invoke() : Bridge.RUNTIME.invoke(hostServices);
        } catch (Throwable failure) {
            throw Bridge.failure(failure);
        }
        return services;
    }

    /** Register a loaded Project, or close it when this scope closed during the load. */
    private LeanProject adopt(Object token) {
        LeanProject project = new LeanProject(this, token);
        synchronized (this) {
            if (!closed) {
                projects.add(project);
                return project;
            }
        }
        project.close();
        throw new IllegalStateException("Lean was closed while the project was loading");
    }

    private void ensureOpen() {
        if (closed) throw new IllegalStateException("Lean is closed");
    }

    synchronized void released(LeanProject project) { projects.remove(project); }

    /** Close every Project; waits for in-flight calls without holding this scope's lock. */
    @Override
    public void close() {
        ArrayList<LeanProject> children;
        synchronized (this) {
            if (closed) return;
            children = new ArrayList<>(projects);
            closed = true;
        }
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
        synchronized (this) { services = null; }
        if (first != null) throw Bridge.failure(first);
    }
}
