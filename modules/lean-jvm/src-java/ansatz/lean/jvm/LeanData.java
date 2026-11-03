package ansatz.lean.jvm;

import java.util.List;

/** Detached immutable nominal value; no public constructor or storage authority. */
public final class LeanData {
    private final LeanType type;
    private final Object capability;
    private final LeanType.Constructor constructor;
    private final List<Object> fields;

    LeanData(LeanType type, Object capability) {
        this.type = type; this.capability = capability;
        constructor = type.constructorAt(type.bridge().constructorIndex(capability));
        fields = new ValueBridge.Fields(type, capability, constructor.fields());
    }
    public LeanType type() { return type; }
    public LeanType.Constructor constructor() { return constructor; }
    public List<Object> fields() { return fields; }
    public Object field(int index) { return fields.get(index); }
    Object capability() { return capability; }
    @Override public boolean equals(Object other) {
        return this == other || other instanceof LeanData data
                && ValueBridge.equal(type, capability, data.type, data.capability);
    }
    @Override public int hashCode() { return ValueBridge.hash(type, capability); }
    @Override public String toString() {
        return "LeanData[type=" + type.nominalId().orElseThrow() + ",constructor="
                + constructor.name() + ",fields=" + fields.size() + "]";
    }
}
