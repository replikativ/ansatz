package prototype;

/** Invocation-local memo: full signed long keys plus a distinct positive kind.
 * Not thread safe; its projector serializes all access. No guest objects retained.
 * Empty and deleted slots are represented in the kind lane, so every long key
 * and every Object value (including null) is representable without collisions.
 */
public final class TypedLongMemo {
    private long[] keys;
    private byte[] kinds;
    private Object[] values;
    private int size;
    private int used;

    public TypedLongMemo() { allocate(16); }

    private void allocate(int n) {
        keys = new long[n];
        kinds = new byte[n];
        values = new Object[n];
    }

    private static int hash(long key, byte kind) {
        long z = key ^ (0x9e3779b97f4a7c15L * kind);
        z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L;
        z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL;
        return (int) (z ^ (z >>> 31));
    }

    private static void validate(byte kind) {
        if (kind <= 0) throw new IllegalArgumentException("Memo kind must be positive");
    }

    public Object get(long key, byte kind, Object absent) {
        validate(kind);
        int mask = keys.length - 1;
        int slot = hash(key, kind) & mask;
        while (kinds[slot] != 0) {
            if (kinds[slot] == kind && keys[slot] == key) return values[slot];
            slot = (slot + 1) & mask;
        }
        return absent;
    }

    public void put(long key, byte kind, Object value) {
        validate(kind);
        // Keep at least one empty slot, even after repeated failed traversals.
        if ((long) (used + 1) * 10 >= (long) keys.length * 7) {
            if ((long) (size + 1) * 10 < (long) keys.length * 5) rehash(keys.length);
            else {
                if (keys.length >= (1 << 29)) throw new IllegalStateException("Memo capacity exceeded");
                rehash(keys.length * 2);
            }
        }
        insert(key, kind, value);
    }

    private void insert(long key, byte kind, Object value) {
        int mask = keys.length - 1;
        int slot = hash(key, kind) & mask;
        int deleted = -1;
        while (kinds[slot] != 0) {
            if (kinds[slot] == kind && keys[slot] == key) {
                values[slot] = value;
                return;
            }
            if (kinds[slot] == -1 && deleted < 0) deleted = slot;
            slot = (slot + 1) & mask;
        }
        if (deleted >= 0) slot = deleted;
        else used++;
        keys[slot] = key;
        kinds[slot] = kind;
        values[slot] = value;
        size++;
    }

    private void rehash(int n) {
        long[] oldKeys = keys;
        byte[] oldKinds = kinds;
        Object[] oldValues = values;
        allocate(n);
        size = 0;
        used = 0;
        for (int i = 0; i < oldKeys.length; i++) {
            if (oldKinds[i] > 0) insert(oldKeys[i], oldKinds[i], oldValues[i]);
        }
    }

    /** Remove unfinished nodes after an exceptional traversal. Identity matters. */
    public void removeValue(Object unfinished) {
        for (int i = 0; i < keys.length; i++) {
            if (kinds[i] > 0 && values[i] == unfinished) {
                kinds[i] = -1;
                values[i] = null;
                size--;
            }
        }
    }

    public int size() { return size; }
    public int capacity() { return keys.length; }
}
