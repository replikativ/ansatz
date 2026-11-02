import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.IPersistentMap;
import clojure.lang.Keyword;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/** Native-prepared stdio fixture through public Java/Clojure APIs, JVM-only. */
public final class StdIOSmoke {
    private static final String MANIFEST = "8378f827716ed1feaa5101b4c9f6bb1cd78433293b62e078a695af94731f1653";
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static byte[] utf8(String text) { return text.getBytes(StandardCharsets.UTF_8); }
    private static Object field(IPersistentMap result, String key) { return result.valAt(Keyword.intern(key)); }
    private static IOResult<?> io(Object value) { return (IOResult<?>) value; }
    private static void bytes(byte[] actual, byte[] expected) { check(Arrays.equals(actual, expected)); }
    public static void main(String[] args) throws Exception {
        LeanFunction retained;
        try (Lean runtime = Lean.open();
             LeanProject project = runtime.loadArtifact(StdIOSmoke.class.getClassLoader(), "lean/stdio.zip", MANIFEST)) {
            retained = project.function("readBytes");
            byte[] supplied = {0, -64, -128, -16, -97, -104, -128, 10};
            byte[] expected = supplied.clone();
            InvocationOptions options = InvocationOptions.stdinBytes(supplied);
            supplied[0] = 99;
            byte[] optionsView = options.stdinBytes(); optionsView[0] = 88;
            for (int i = 0; i < 3; i++) {
                IOResult<?> read = io(retained.invokeWith(options, 32L));
                bytes((byte[]) read.value(), expected);
                check(read.stdout().isEmpty() && read.stderr().isEmpty());
            }
            bytes((byte[]) io(retained.invoke(32L)).value(), new byte[0]);
            bytes((byte[]) io(retained.invokeWith(options, 0L)).value(), new byte[0]);
            bytes((byte[]) io(retained.invokeWith(options, 2L)).value(), new byte[]{0, -64});
            check(io(project.callWith("readLine", InvocationOptions.stdinText("A\u0000β\r\nrest")))
                .value().equals("A\u0000β\r\n"));
            check(io(project.callWith("readLine", InvocationOptions.stdinText("last"))).value().equals("last"));
            check(io(project.call("readLine")).value().equals(""));
            check(io(project.callWith("readLine", InvocationOptions.stdinBytes(new byte[]{-64, -128, 10})))
                .value().equals("�\n"));
            IOResult<?> echo = io(project.callWith("echoBytes", options));
            bytes(echo.stdoutBytes(), expected); check(echo.stderrBytes().length == 0);
            byte[] outputView = echo.stdoutBytes(); outputView[0] = 77;
            bytes(echo.stdoutBytes(), expected);
            IOResult<?> split = io(project.callWith("splitUtf8", InvocationOptions.empty().withOutputLimits(4, 0)));
            check(split.stdout().equals("😀")); bytes(split.stdoutBytes(), utf8("😀"));
            IOResult<?> invalid = io(project.call("invalidUtf8"));
            bytes(invalid.stdoutBytes(), new byte[]{-64, -128});
            check(io(project.call("wrongDirectionCaught")).value().equals(Boolean.TRUE));
            IOResult<?> message = io(project.callWith("message", InvocationOptions.empty().withOutputLimits(6, 0)));
            check(message.stdout().equals("hello\n")); bytes(message.stdoutBytes(), utf8("hello\n"));
            IOResult<?> error = io(project.callWith("errorMessage", InvocationOptions.empty().withOutputLimits(0, 6)));
            check(error.stdoutBytes().length == 0 && error.stderr().equals("error\n"));
            byte[] errorView = error.stderrBytes(); errorView[0] = 0; bytes(error.stderrBytes(), utf8("error\n"));
            try { InvocationOptions.stdinText("\ud800"); throw new AssertionError("invalid text"); }
            catch (IllegalArgumentException expectedFailure) { checks++; }
            check(io(project.call("message")).stdout().equals("hello\n"));

            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IFn call = Clojure.var("ansatz.lean.jvm", "call-with-options");
            IPersistentMap line = (IPersistentMap) call.invoke(project, "readLine", Clojure.read("{:stdin \"Ada\\n\"}"));
            check(field(line, "value").equals("Ada\n"));
            bytes((byte[]) field(line, "stdout-bytes"), new byte[0]);
            byte[] clojureInput = {1, 2, 3};
            Object clojureOptions = Clojure.var("clojure.core", "assoc").invoke(Clojure.read("{}"), Keyword.intern("stdin-bytes"), clojureInput);
            IFn function = (IFn) Clojure.var("ansatz.lean.jvm", "function").invoke(project, "readBytes", clojureOptions);
            clojureInput[0] = 9;
            for (int i = 0; i < 2; i++) {
                IPersistentMap result = (IPersistentMap) function.invoke(32L);
                bytes((byte[]) field(result, "value"), new byte[]{1, 2, 3});
            }
            IPersistentMap clojureRaw = (IPersistentMap) call.invoke(project, "invalidUtf8", Clojure.read("{}"));
            bytes((byte[]) field(clojureRaw, "stdout-bytes"), new byte[]{-64, -128});
            IPersistentMap ordinary = (IPersistentMap) Clojure.var("ansatz.lean.jvm", "call").invoke(project, "message");
            check(ordinary.count() == 3 && field(ordinary, "stdout").equals("hello\n"));
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        try { retained.invokeWith(InvocationOptions.empty(), 1L); throw new AssertionError("closed handle"); }
        catch (IllegalStateException expected) { check(expected.getMessage().contains("closed")); }
        System.out.println("STDIO_SMOKE checks=" + checks + "; public Java/Clojure APIs, JVM-only artifact");
    }
}
