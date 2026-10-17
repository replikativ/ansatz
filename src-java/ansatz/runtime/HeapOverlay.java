package ansatz.runtime;

import clojure.lang.IPersistentMap;
import clojure.lang.IMapEntry;
import clojure.lang.PersistentHashMap;
import clojure.lang.PersistentArrayMap;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiFunction;

/** Single-threaded local heap over one immutable snapshot, never another overlay.
 * No guest RC operations occur here. Values are borrowed node maps; mutable field
 * storage remains the interpreter's responsibility. Not serializable.
 */
public final class HeapOverlay extends AbstractMap<Object, Object> {
    private static final Object ABSENT = new Object();
    private static final Object DELETED = new Object();
    private final IPersistentMap base;
    private final Map<?, ?> baseMap;
    private final HashMap<Object, Object> writes = new HashMap<>();
    private final Set<Object> dirty;
    private final boolean canonicalLongBase;
    private boolean baseVisible = true;
    private int count;

    public HeapOverlay(IPersistentMap base, Set<?> dirty) {
        this(base, dirty, false);
    }

    /** canonicalLongBase is an internal caller attestation from the existing
     * snapshot validation pass: EVERY base key is a java.lang.Long. */
    @SuppressWarnings("unchecked")
    public HeapOverlay(IPersistentMap base, Set<?> dirty, boolean canonicalLongBase) {
        this.base = Objects.requireNonNull(base, "persistent heap base");
        if (!(base instanceof Map)) {
            throw new IllegalArgumentException("Persistent heap base must implement java.util.Map");
        }
        this.baseMap = (Map<?, ?>) base;
        this.dirty = (Set<Object>) Objects.requireNonNull(dirty, "dirty IDs");
        this.count = base.count();
        // Comparator-based/custom persistent maps can equate DISTINCT Longs.
        // Only standard concrete maps admit this allocation-free proof.
        this.canonicalLongBase = canonicalLongBase &&
            (base.getClass() == PersistentHashMap.class || base.getClass() == PersistentArrayMap.class);
    }

    private Object lookupBase(Object key) {
        // A Clojure persistent map equates e.g. Long(1) and Integer(1), whereas
        // the old eager HashMap (and writes below) uses Java equals. Inspect the
        // stored key to preserve ONE key relation throughout this Java Map.
        if (!baseVisible) return ABSENT;
        // Actual guest IDs are Long. This proof avoids entryAt's temporary
        // Map.Entry allocation on every hot node lookup.
        if (canonicalLongBase) {
            if (key == null || key instanceof Long) return base.valAt(key, ABSENT);
            if (key instanceof Number) return ABSENT;
        }
        IMapEntry entry = base.entryAt(key);
        return entry != null && Objects.equals(key, entry.key()) ? entry.val() : ABSENT;
    }

    private Object lookup(Object key) {
        Object value = writes.get(key);
        if (value != null || writes.containsKey(key)) {
            return value == DELETED ? ABSENT : value;
        }
        return lookupBase(key);
    }

    @Override public int size() { return count; }
    @Override public boolean containsKey(Object key) { return lookup(key) != ABSENT; }
    @Override public Object get(Object key) {
        Object value = lookup(key);
        return value == ABSENT ? null : value;
    }
    @Override public Object put(Object key, Object value) {
        Object old = lookup(key);
        writes.put(key, value);
        if (old == ABSENT) count++;
        dirty.add(key);
        return old == ABSENT ? null : old;
    }
    @Override public Object remove(Object key) {
        Object old = lookup(key);
        if (old == ABSENT) return null;
        if (lookupBase(key) != ABSENT) writes.put(key, DELETED);
        else writes.remove(key);
        count--;
        dirty.add(key);
        return old;
    }
    @Override public void clear() {
        // Rare explicit Map operation. Delta freeze must see every deletion.
        dirty.addAll(keysSnapshot());
        writes.clear();
        baseVisible = false;
        count = 0;
    }

    private ArrayList<Object> keysSnapshot() {
        ArrayList<Object> keys = new ArrayList<>(count);
        if (baseVisible) {
            for (Object key : baseMap.keySet()) {
                if (lookup(key) != ABSENT) keys.add(key);
            }
        }
        for (Object key : writes.keySet()) {
            if ((lookupBase(key) == ABSENT) && lookup(key) != ABSENT) keys.add(key);
        }
        return keys;
    }

    @Override public Set<Entry<Object, Object>> entrySet() {
        // Live view; each iterator snapshots keys, never mutable backing entries.
        // Concurrent structural mutation is unspecified (single-threaded Map).
        return new AbstractSet<Entry<Object, Object>>() {
            @Override public int size() { return HeapOverlay.this.size(); }
            @Override public void clear() { HeapOverlay.this.clear(); }
            @Override public boolean contains(Object candidate) {
                if (!(candidate instanceof Entry)) return false;
                Entry<?, ?> e = (Entry<?, ?>) candidate;
                Object value = lookup(e.getKey());
                return value != ABSENT && Objects.equals(value, e.getValue());
            }
            @Override public Iterator<Entry<Object, Object>> iterator() {
                final Iterator<Object> keys = keysSnapshot().iterator();
                return new Iterator<Entry<Object, Object>>() {
                    private Object last;
                    private boolean removable;
                    @Override public boolean hasNext() { return keys.hasNext(); }
                    @Override public Entry<Object, Object> next() {
                        if (!keys.hasNext()) throw new NoSuchElementException();
                        last = keys.next();
                        removable = true;
                        return new SimpleImmutableEntry<>(last, HeapOverlay.this.get(last));
                    }
                    @Override public void remove() {
                        if (!removable) throw new IllegalStateException();
                        HeapOverlay.this.remove(last);
                        removable = false;
                    }
                };
            }
        };
    }

    @Override public void replaceAll(BiFunction<? super Object, ? super Object, ?> function) {
        Objects.requireNonNull(function);
        // AbstractMap's immutable entries cannot be used by Map's setValue-based
        // default. All writes here, other defaults and view removals mark dirty.
        for (Object key : keysSnapshot()) put(key, function.apply(key, get(key)));
    }
}
