package ansatz.lean.jvm;

import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.time.Duration;
import java.util.Objects;

/**
 * Immutable per-invocation policy: finite stdin, captured output limits, the
 * cooperative execution budget and the panic policy. No OS handles.
 */
public final class InvocationOptions {
    public static final int MAX_STDIN_BYTES = 1024 * 1024;
    public static final int MAX_OUTPUT_BYTES = 16 * 1024 * 1024;
    /** Default interpreter instruction budget of one call. */
    public static final long DEFAULT_INSTRUCTIONS = 2_000_000L;
    /** Largest accepted instruction budget (2^40). */
    public static final long MAX_INSTRUCTIONS = 1L << 40;
    /** Default wall-clock budget of one call. */
    public static final Duration DEFAULT_TIME = Duration.ofSeconds(5);
    /** Largest accepted wall-clock budget. */
    public static final Duration MAX_TIME = Duration.ofMinutes(10);
    private static final InvocationOptions EMPTY = new InvocationOptions(new byte[0], MAX_OUTPUT_BYTES, MAX_OUTPUT_BYTES,
            DEFAULT_INSTRUCTIONS, DEFAULT_TIME.toNanos(), false);
    private final byte[] input;
    private final int stdoutLimit;
    private final int stderrLimit;
    private final long instructions;
    private final long timeNanos;
    private final boolean failOnPanic;

    private InvocationOptions(byte[] input, int stdoutLimit, int stderrLimit, long instructions, long timeNanos,
                              boolean failOnPanic) {
        Objects.requireNonNull(input, "stdin");
        if (input.length > MAX_STDIN_BYTES) throw new IllegalArgumentException("stdin exceeds one MiB");
        if (stdoutLimit < 0 || stdoutLimit > MAX_OUTPUT_BYTES || stderrLimit < 0 || stderrLimit > MAX_OUTPUT_BYTES)
            throw new IllegalArgumentException("Output limits must be between zero and sixteen MiB per channel");
        checkBudget(instructions, timeNanos);
        this.input = input.clone();
        this.stdoutLimit = stdoutLimit;
        this.stderrLimit = stderrLimit;
        this.instructions = instructions;
        this.timeNanos = timeNanos;
        this.failOnPanic = failOnPanic;
    }

    static void checkBudget(long instructions, long timeNanos) {
        if (instructions < 1 || instructions > MAX_INSTRUCTIONS)
            throw new IllegalArgumentException("Instruction budget must be between 1 and 2^40");
        if (timeNanos < 1 || timeNanos > MAX_TIME.toNanos())
            throw new IllegalArgumentException("Time budget must be positive and at most ten minutes");
    }

    static long nanos(Duration time) {
        Objects.requireNonNull(time, "time");
        if (time.isNegative() || time.isZero() || time.compareTo(MAX_TIME) > 0)
            throw new IllegalArgumentException("Time budget must be positive and at most ten minutes");
        return time.toNanos();
    }

    /** Empty stdin, sixteen MiB per output channel, the default budget, native panic semantics. */
    public static InvocationOptions empty() { return EMPTY; }
    public static InvocationOptions stdinBytes(byte[] input) {
        return EMPTY.withStdinBytes(input);
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
    public InvocationOptions withStdinBytes(byte[] input) {
        return new InvocationOptions(input, stdoutLimit, stderrLimit, instructions, timeNanos, failOnPanic);
    }
    public InvocationOptions withOutputLimits(int stdoutBytes, int stderrBytes) {
        return new InvocationOptions(input, stdoutBytes, stderrBytes, instructions, timeNanos, failOnPanic);
    }
    /**
     * Replace the cooperative budget. A call that exceeds either bound fails with
     * {@code ResourceLimit} and retires its Project (see {@link LeanProject#restart()}).
     */
    public InvocationOptions withBudget(long instructions, Duration time) {
        return new InvocationOptions(input, stdoutLimit, stderrLimit, instructions, nanos(time), failOnPanic);
    }
    /**
     * By default a reached {@code panic!} behaves as in native Lean: its message
     * is written to captured stderr and execution continues with the default
     * value. With {@code true} the call instead fails with {@code LeanPanic},
     * like {@code LEAN_ABORT_ON_PANIC}, and retires its Project.
     */
    public InvocationOptions withFailOnPanic(boolean fail) {
        return new InvocationOptions(input, stdoutLimit, stderrLimit, instructions, timeNanos, fail);
    }
    public byte[] stdinBytes() { return input.clone(); }
    public int stdoutLimitBytes() { return stdoutLimit; }
    public int stderrLimitBytes() { return stderrLimit; }
    public long instructionBudget() { return instructions; }
    public Duration timeBudget() { return Duration.ofNanos(timeNanos); }
    public long timeBudgetNanos() { return timeNanos; }
    public boolean failOnPanic() { return failOnPanic; }
}
