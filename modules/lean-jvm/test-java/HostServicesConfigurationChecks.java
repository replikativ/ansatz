import ansatz.lean.jvm.HostServices;
import ansatz.lean.jvm.ReadOnlyFiles;
import java.nio.file.Path;

/** JDK-only configuration checks; does not load Lean, its bridge, or any provider. */
public final class HostServicesConfigurationChecks {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static void invalid(Runnable action) {
        try { action.run(); throw new AssertionError("Invalid configuration accepted"); }
        catch (IllegalArgumentException expected) { checks++; }
    }
    public static void main(String[] ignored) {
        ReadOnlyFiles original = ReadOnlyFiles.root(Path.of("deliberately-nonexistent-config-root"));
        check(original.root().isAbsolute());
        check(original.workingDirectory().equals(Path.of(".")));
        check(original.maxHandles() == 32 && original.maxReadBytes() == 1048576);
        check(original.maxTotalBytes() == 16L * 1048576 && original.maxOperations() == 10000 && original.maxPathBytes() == 4096);
        ReadOnlyFiles modified = original.workingDirectory(Path.of("examples")).limits(2, 17, 0, 1, 12);
        check(modified != original && modified.root().equals(original.root()));
        check(modified.workingDirectory().equals(Path.of("examples")) && original.workingDirectory().equals(Path.of(".")));
        check(modified.maxHandles() == 2 && modified.maxReadBytes() == 17 && modified.maxTotalBytes() == 0
                && modified.maxOperations() == 1 && modified.maxPathBytes() == 12);
        check(original.maxHandles() == 32 && original.maxTotalBytes() == 16L * 1048576);
        HostServices.Builder builder = HostServices.builder();
        HostServices empty = builder.build(), first = builder.files(original).build(), second = builder.files(modified).build();
        check(empty.files() == null && first.files() == original && second.files() == modified);
        invalid(() -> original.workingDirectory(Path.of("/absolute")));
        invalid(() -> original.workingDirectory(Path.of("a/../b")));
        invalid(() -> original.limits(0, 1, 1, 1, 1));
        invalid(() -> original.limits(1025, 1, 1, 1, 1));
        invalid(() -> original.limits(1, 0, 1, 1, 1));
        invalid(() -> original.limits(1, 16777217, 1, 1, 1));
        invalid(() -> original.limits(1, 1, -1, 1, 1));
        invalid(() -> original.limits(1, 1, 1, 0, 1));
        invalid(() -> original.limits(1, 1, 1, 1, 0));
        invalid(() -> original.limits(1, 1, 1, 1, 1048577));
        ReadOnlyFiles upper = original.limits(1024, 16777216, Long.MAX_VALUE, Long.MAX_VALUE, 1048576);
        check(upper.maxOperations() == Long.MAX_VALUE);
        try { HostServices.builder().files(null); throw new AssertionError("null accepted"); }
        catch (NullPointerException expected) { checks++; }
        System.out.println("HOST_SERVICES_CONFIGURATION_CHECKS " + checks);
    }
}
