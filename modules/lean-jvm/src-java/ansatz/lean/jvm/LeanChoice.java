package ansatz.lean.jvm;

import java.util.Objects;

/** A Sum/Except branch with an explicit tag; Unit payloads use LeanUnit.INSTANCE. */
public final class LeanChoice {
    private final boolean left;
    private final Object value;
    private LeanChoice(boolean left, Object value) {
        this.left = left;
        this.value = Objects.requireNonNull(value, "branch payload");
    }
    public static LeanChoice left(Object value) { return new LeanChoice(true, value); }
    public static LeanChoice right(Object value) { return new LeanChoice(false, value); }
    public boolean isLeft() { return left; }
    public Object value() { return value; }
    @Override public String toString() { return (left ? "Left[" : "Right[") + value + "]"; }
}
