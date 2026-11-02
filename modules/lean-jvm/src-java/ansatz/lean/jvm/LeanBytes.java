package ansatz.lean.jvm;

/** Immutable live bytes in certified canonical storage. Copies are explicit. */
public final class LeanBytes {
    private final ValueBridge bridge;
    private final Object capability;

    LeanBytes(ValueBridge bridge, Object capability) {
        this.bridge = bridge; this.capability = capability;
    }
    public static LeanBytes copyOf(byte[] source) { return ValueBridge.copyBytes(source); }
    public int size() { return bridge.size(capability); }
    public int get(int index) { return bridge.byteAt(capability, index); }
    public byte[] toByteArray() { return bridge.copyBytesOut(capability); }
    ValueBridge bridge() { return bridge; }
    Object capability() { return capability; }
    @Override public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof LeanBytes bytes) || size() != bytes.size()) return false;
        for (int i = 0; i < size(); i++) if (get(i) != bytes.get(i)) return false;
        return true;
    }
    @Override public int hashCode() {
        int h = 1;
        for (int i = 0, n = size(); i < n; i++) h = 31 * h + (byte) get(i);
        return h;
    }
    @Override public String toString() { return "LeanBytes[size=" + size() + "]"; }
}
