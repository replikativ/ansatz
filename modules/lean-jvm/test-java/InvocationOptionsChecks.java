import ansatz.lean.jvm.InvocationOptions;
import ansatz.lean.jvm.IOResult;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/** Value-only options and raw-output snapshots, without constructing a runtime. */
public final class InvocationOptionsChecks {
    private static int checks;
    private static void check(boolean value) { checks++; if (!value) throw new AssertionError("check " + checks); }
    private static void refuse(Runnable action) {
        try { action.run(); throw new AssertionError("Expected refusal"); }
        catch (IllegalArgumentException expected) { checks++; }
    }
    public static void main(String[] args) {
        check(InvocationOptions.empty().stdinBytes().length == 0);
        check(InvocationOptions.empty().stdoutLimitBytes() == 16 * 1024 * 1024);
        byte[] input = {1, 2, 3};
        InvocationOptions options = InvocationOptions.stdinBytes(input);
        input[0] = 9;
        byte[] first = options.stdinBytes();
        first[1] = 9;
        check(Arrays.equals(options.stdinBytes(), new byte[]{1, 2, 3}));
        InvocationOptions limited = options.withOutputLimits(0, 42);
        check(limited.stdoutLimitBytes() == 0 && limited.stderrLimitBytes() == 42);
        check(Arrays.equals(limited.stdinBytes(), new byte[]{1, 2, 3}));
        check(options.stdoutLimitBytes() == InvocationOptions.MAX_OUTPUT_BYTES);
        check(Arrays.equals(InvocationOptions.stdinText("λ😀\0\r\n").stdinBytes(), "λ😀\0\r\n".getBytes(StandardCharsets.UTF_8)));
        check(InvocationOptions.stdinBytes(new byte[InvocationOptions.MAX_STDIN_BYTES]).stdinBytes().length == InvocationOptions.MAX_STDIN_BYTES);
        refuse(() -> InvocationOptions.stdinBytes(new byte[InvocationOptions.MAX_STDIN_BYTES + 1]));
        refuse(() -> InvocationOptions.stdinText("\ud800"));
        refuse(() -> InvocationOptions.stdinText("\udc00"));
        refuse(() -> InvocationOptions.stdinText("λ".repeat(InvocationOptions.MAX_STDIN_BYTES)));
        refuse(() -> options.withOutputLimits(-1, 0));
        refuse(() -> options.withOutputLimits(0, InvocationOptions.MAX_OUTPUT_BYTES + 1));
        byte[] raw = {(byte)0xc0, (byte)0x80};
        IOResult<Integer> result = new IOResult<>(42, raw, new byte[]{0, 10});
        raw[0] = 0;
        check(result.value().equals(42));
        check(result.stdout().equals("\ufffd\ufffd")); // documented Java UTF-8 text view
        check(Arrays.equals(result.stdoutBytes(), new byte[]{(byte)0xc0, (byte)0x80}));
        byte[] output = result.stderrBytes(); output[0] = 9;
        check(Arrays.equals(result.stderrBytes(), new byte[]{0, 10}));
        IOResult<String> legacy = new IOResult<>("ok", "λ😀\0", "");
        check(legacy.stdout().equals("λ😀\0") && Arrays.equals(legacy.stdoutBytes(), "λ😀\0".getBytes(StandardCharsets.UTF_8)));
        System.out.println("INVOCATION_OPTIONS_CHECKS " + checks);
    }
}
