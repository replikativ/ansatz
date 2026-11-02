import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IPersistentMap;
import clojure.lang.Keyword;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

/** Authored writer via an application-JAR artifact and public Java/Clojure calls. */
public final class WriterSmoke {
    private static final String MANIFEST = "891fb3a54939a179033d8edc2bb32ece69e5be2f7f55d24119b063cdcac378f7";
    private static final String INPUT = "hello é\0雪\n";
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("Writer check " + checks); }
    private static LeanProject load(Lean runtime) throws Exception {
        return runtime.loadArtifact(WriterSmoke.class.getClassLoader(), "lean/writer.zip", MANIFEST);
    }
    private static void files(Path root, String output) throws Exception {
        check(Arrays.equals(Files.readAllBytes(root.resolve(output)), ("processed\n" + INPUT).getBytes(StandardCharsets.UTF_8)));
        check(Arrays.equals(Files.readAllBytes(root.resolve(output + ".bin")), new byte[]{0,(byte)255}));
        check(Arrays.equals(Files.readAllBytes(root.resolve(output + ".new")), "é\0雪".getBytes(StandardCharsets.UTF_8)));
        check(Files.readString(root.resolve(output + ".log")).equals("written\ndone\n"));
        check(Files.readString(root.resolve("input.txt")).equals(INPUT));
    }
    public static void main(String[] ignored) throws Exception {
        Path root = Files.createTempDirectory(Path.of(".").toAbsolutePath(), "writer-");
        try {
            Files.writeString(root.resolve("input.txt"), INPUT);
            HostServices services = HostServices.builder().fileAccess(FileAccess.readWrite(root)).build();
            try (Lean runtime = Lean.open(services); LeanProject project = load(runtime)) {
                IOResult<?> r = (IOResult<?>) project.call("main", List.of("input.txt", "output.txt"));
                check(r.value().equals(BigInteger.ZERO));
                check(r.stdout().equals("bytes=2; exists=17\n")); check(r.stderr().isEmpty());
                files(root, "output.txt");
                Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
                IPersistentMap c = (IPersistentMap) Clojure.var("ansatz.lean.jvm", "call")
                        .invoke(project, "main", Clojure.read("[\"input.txt\" \"clojure.txt\"]"));
                check(c.valAt(Keyword.intern("value")).equals(BigInteger.ZERO));
                check(c.valAt(Keyword.intern("stdout")).equals("bytes=2; exists=17\n"));
                check(c.valAt(Keyword.intern("stderr")).equals("")); files(root, "clojure.txt");
            }
            try (Lean runtime = Lean.open(HostServices.builder().files(ReadOnlyFiles.root(root)).build());
                 LeanProject project = load(runtime)) {
                try { project.call("main", List.of("input.txt", "denied.txt")); throw new AssertionError("Write authority accepted"); }
                catch (LeanException failure) { check(failure.code().equals("FilesystemPolicy")); check(failure.getCause() == null); }
                check(!Files.exists(root.resolve("denied.txt"))); files(root, "output.txt");
            }
        } finally {
            // All Project/runtime scopes close before fixture removal.
            try (var paths = Files.walk(root)) {
                for (Path file : paths.sorted(Comparator.reverseOrder()).toList()) Files.deleteIfExists(file);
            }
        }
        check(!Files.exists(root));
        System.out.println("WRITER_SMOKE checks=" + checks + "; public Java/Clojure writable artifact and read-only refusal");
    }
}
