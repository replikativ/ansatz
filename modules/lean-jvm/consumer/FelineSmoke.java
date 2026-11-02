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

/** Unchanged two-file Feline through public APIs; artifact-only, without a toolchain. */
public final class FelineSmoke {
    private static final String MANIFEST = "addd36008695cd8494e47eaf8495baff89631621272fbb4aabb736bfdd59335d";
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static byte[] utf8(String text) { return text.getBytes(StandardCharsets.UTF_8); }
    @FunctionalInterface private interface Attempt { void run() throws Exception; }
    private static void refuse(String code, Attempt attempt) throws Exception {
        try { attempt.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException error) { check(code.equals(error.code())); check(error.getCause() == null); }
    }
    private static LeanProject load(Lean runtime) throws Exception {
        return runtime.loadArtifact(FelineSmoke.class.getClassLoader(), "lean/feline.zip", MANIFEST);
    }
    private static HostServices services(ReadOnlyFiles files) { return HostServices.builder().files(files).build(); }
    private static void result(Object value, int exit, byte[] stdout, String stderr) {
        IOResult<?> result = (IOResult<?>) value;
        check(result.value().equals(BigInteger.valueOf(exit)));
        check(Arrays.equals(result.stdoutBytes(), stdout)); check(result.stderr().equals(stderr));
    }
    public static void main(String[] ignored) throws Exception {
        Path root = Files.createTempDirectory(Path.of(".").toAbsolutePath(), "feline-");
        LeanFunction retained;
        try {
            byte[] binary = {0,-64,-128,-16,-97,-104,-128,10};
            Files.write(root.resolve("first"), utf8("oneλ\n")); Files.write(root.resolve("second"), utf8("two\n"));
            Files.write(root.resolve("empty"), new byte[0]); Files.write(root.resolve("binary"), binary);
            Files.createDirectory(root.resolve("directory"));
            try (Lean none = Lean.open()) { refuse("CapabilityMissing", () -> load(none)); }
            try (Lean runtime = Lean.open(services(ReadOnlyFiles.root(root)));
                 LeanProject healthy = load(runtime)) {
                retained = healthy.function("main"); check(retained.arity() == 1);
                for (int i=0;i<3;i++) result(retained.invoke(List.of("first","second")),0,utf8("oneλ\ntwo\n"),"");
                result(retained.invoke(List.of("empty")),0,new byte[0],"");
                result(retained.invokeWith(InvocationOptions.stdinText("stdin\n"),List.of()),0,utf8("stdin\n"),"");
                result(retained.invokeWith(InvocationOptions.stdinText("stdin\n"),List.of("first","-","second")),
                       0,utf8("oneλ\nstdin\ntwo\n"),"");
                result(retained.invokeWith(InvocationOptions.stdinText("once"),List.of("-","-")),0,utf8("once"),"");
                result(retained.invoke(List.of("missing","first")),1,utf8("oneλ\n"),"File not found: missing\n");
                result(retained.invoke(List.of("binary")),0,binary,"");
                Clojure.var("clojure.core","require").invoke(Clojure.read("ansatz.lean.jvm"));
                IPersistentMap clojure = (IPersistentMap) Clojure.var("ansatz.lean.jvm","call")
                    .invoke(healthy,"main",Clojure.read("[\"first\"]"));
                check(clojure.valAt(Keyword.intern("value")).equals(BigInteger.ZERO));
                check(clojure.valAt(Keyword.intern("stdout")).equals("oneλ\n"));
                check(clojure.valAt(Keyword.intern("stderr")).equals(""));
                try (LeanProject failed = load(runtime)) {
                    refuse("ResourceLimit", () -> failed.callWith("main",InvocationOptions.empty().withOutputLimits(1,0),List.of("first")));
                }
                checks++; // Failed output branch must close its real file resources.
                result(retained.invoke(List.of("second")),0,utf8("two\n"),"");
                try (LeanProject failed = load(runtime)) {
                    refuse("FilesystemPolicy", () -> failed.call("main",List.of("directory")));
                }
                checks++;
                result(retained.invoke(List.of("first")),0,utf8("oneλ\n"),"");
                check(Clojure.var("clojure.core","find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
            }
            try { retained.invoke(List.of("first")); throw new AssertionError("Closed function accepted"); }
            catch (IllegalStateException expected) { check(expected.getMessage().contains("closed")); }
            try (Lean limited = Lean.open(services(ReadOnlyFiles.root(root).limits(4,1048576,0,1000,4096)));
                 LeanProject failed = load(limited)) {
                refuse("ResourceLimit", () -> failed.call("main",List.of("first")));
            }
            checks++;
            check(Clojure.var("clojure.core","find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        } finally {
            // Try every deletion only after all Project/runtime scopes have closed.
            try (var paths = Files.walk(root)) {
                for (Path path : paths.sorted(Comparator.reverseOrder()).toList()) {
                    try { Files.deleteIfExists(path); } catch (java.io.IOException ignoredCleanup) { }
                }
            } catch (java.io.IOException ignoredCleanup) { }
        }
        System.out.println("FELINE_SMOKE checks=" + checks + "; public Java/Clojure APIs, JVM-only filesystem artifact");
    }
}
