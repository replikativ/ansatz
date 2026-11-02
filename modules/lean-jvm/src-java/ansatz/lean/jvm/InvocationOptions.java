package ansatz.lean.jvm;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.util.Objects;

/** Immutable, bounded input and output policy for one invocation. No OS handles. */
public final class InvocationOptions {
    public static final int MAX_STDIN_BYTES = 1024 * 1024;
    public static final int MAX_OUTPUT_BYTES = 16 * 1024 * 1024;
    private static final InvocationOptions EMPTY = new InvocationOptions(new byte[0], MAX_OUTPUT_BYTES, MAX_OUTPUT_BYTES);
    private final byte[] input;
    private final int stdoutLimit;
    private final int stderrLimit;

    private InvocationOptions(byte[] input, int stdoutLimit, int stderrLimit) {
        Objects.requireNonNull(input, "stdin");
        if (input.length > MAX_STDIN_BYTES) throw new IllegalArgumentException("stdin exceeds one MiB");
        if (stdoutLimit < 0 || stdoutLimit > MAX_OUTPUT_BYTES || stderrLimit < 0 || stderrLimit > MAX_OUTPUT_BYTES)
            throw new IllegalArgumentException("Output limits must be between zero and sixteen MiB per channel");
        this.input = input.clone();
        this.stdoutLimit = stdoutLimit;
        this.stderrLimit = stderrLimit;
    }

    public static InvocationOptions empty() { return EMPTY; }
    public static InvocationOptions stdinBytes(byte[] input) {
        return new InvocationOptions(input, MAX_OUTPUT_BYTES, MAX_OUTPUT_BYTES);
    }
    public static InvocationOptions stdinText(String input) {
        Objects.requireNonNull(input, "stdin");
        if (input.length() > MAX_STDIN_BYTES) throw new IllegalArgumentException("stdin exceeds one MiB");
        try {
            ByteBuffer encoded = StandardCharsets.UTF_8.newEncoder()
                .onMalformedInput(CodingErrorAction.REPORT).onUnmappableCharacter(CodingErrorAction.REPORT)
                .encode(CharBuffer.wrap(input));
            if (encoded.remaining() > MAX_STDIN_BYTES) throw new IllegalArgumentException("stdin exceeds one MiB");
            byte[] bytes = new byte[encoded.remaining()];
            encoded.get(bytes);
            return stdinBytes(bytes);
        } catch (CharacterCodingException invalid) {
            throw new IllegalArgumentException("stdin text must contain valid Unicode", invalid);
        }
    }
    public InvocationOptions withOutputLimits(int stdoutBytes, int stderrBytes) {
        return new InvocationOptions(input, stdoutBytes, stderrBytes);
    }
    public byte[] stdinBytes() { return input.clone(); }
    public int stdoutLimitBytes() { return stdoutLimit; }
    public int stderrLimitBytes() { return stderrLimit; }
}
