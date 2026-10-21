package ansatz.runtime;

import clojure.lang.IPersistentMap;
import clojure.lang.IMeta;
import clojure.lang.IMapEntry;
import clojure.lang.Keyword;
import clojure.lang.PersistentArrayMap;
import clojure.lang.PersistentHashMap;
import clojure.lang.PersistentVector;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

/** Local lazy globals boundary, not a guest authority or serialized capability.
 * Read-only canonical globals borrow one immutable base. The first mutation,
 * unsupported lookup key, or Map-view request creates exactly HashMap(base).
 * Thereafter all Map operations use that same HashMap, including live views and
 * Java's numeric key equality, iteration, default-mutator and callback behavior.
 * Values remain borrowed exactly as in the former eager HashMap conversion.
 */
public final class GlobalsOverlay extends AbstractMap<Object, Object> {
    private IPersistentMap base;
    private Map<?, ?> baseMap;
    private HashMap<Object, Object> mutable;
    private boolean canonicalKeys = true;

    private static final int HINT_LIMIT = 256;
    private static final HashMap<Integer, ArrayList<Hint>> HINTS = new HashMap<>();
    private static final ReferenceQueue<IPersistentMap> QUEUE = new ReferenceQueue<>();
    private static int hintCount;
    private static final class Hint extends WeakReference<IPersistentMap> {
        final int hash;
        final boolean eligible;
        Hint(IPersistentMap value, boolean eligible) {
            super(value, QUEUE);
            hash = System.identityHashCode(value);
            this.eligible = eligible;
        }
    }

    private GlobalsOverlay(IPersistentMap base) {
        this.base = base;
        this.baseMap = (Map<?, ?>) base;
    }

    /** Only immutable canonical keys: numeric keys are Long, never Integer or
     * another Clojure-equivalent/Java-distinct number. No graph is retained. */
    private static boolean canonicalKey(Object key) {
        if (key instanceof String || key instanceof Keyword || key instanceof Long) return true;
        if (key == null || key.getClass() != PersistentVector.class) return false;
        ArrayDeque<Object> pending = new ArrayDeque<>();
        pending.push(key);
        int remaining = 4096;
        while (!pending.isEmpty()) {
            Object value = pending.pop();
            if (--remaining < 0) return false;
            if (value instanceof String || value instanceof Keyword || value instanceof Long) continue;
            if (value == null || value.getClass() != PersistentVector.class) return false;
            PersistentVector vector = (PersistentVector) value;
            // Shared vector DAGs can describe exponentially many paths while
            // their already cached map hashes are cheap. Bound both traversal
            // work and queued children, then conservatively use the eager path.
            if (vector.count() > remaining - pending.size()) return false;
            for (int i = 0; i < vector.count(); i++) {
                Object child = vector.nth(i);
                if (child == null) return false;
                pending.push(child);
            }
        }
        return true;
    }

    private static void cleanHints() {
        Hint dead;
        while ((dead = (Hint) QUEUE.poll()) != null) {
            ArrayList<Hint> bucket = HINTS.get(dead.hash);
            if (bucket != null && bucket.remove(dead)) {
                hintCount--;
                if (bucket.isEmpty()) HINTS.remove(dead.hash);
            }
        }
    }

    private static void remember(IPersistentMap map, boolean eligible) {
        synchronized (HINTS) {
            cleanHints();
            int hash = System.identityHashCode(map);
            ArrayList<Hint> bucket = HINTS.get(hash);
            if (bucket != null) {
                for (Hint hint : bucket) if (hint.get() == map) return;
            }
            if (hintCount >= HINT_LIMIT) {
                HINTS.clear();
                hintCount = 0;
                bucket = null;
            }
            if (bucket == null) {
                bucket = new ArrayList<>();
                HINTS.put(hash, bucket);
            }
            bucket.add(new Hint(map, eligible));
            hintCount++;
        }
    }

    private static boolean eligible(Map<?, ?> map) {
        if (map.getClass() != PersistentHashMap.class && map.getClass() != PersistentArrayMap.class) return false;
        // The former into{} boundary dropped metadata. Do not preserve it as an
        // incidental consequence of unchanged-base reuse.
        if (((IMeta) map).meta() != null) return false;
        IPersistentMap persistent = (IPersistentMap) map;
        synchronized (HINTS) {
            cleanHints();
            ArrayList<Hint> bucket = HINTS.get(System.identityHashCode(map));
            if (bucket != null) {
                for (Hint hint : bucket) if (hint.get() == map) return hint.eligible;
            }
        }
        boolean eligible = true;
        for (Object key : map.keySet()) if (!canonicalKey(key)) { eligible = false; break; }
        remember(persistent, eligible);
        return eligible;
    }

    public static Map<Object, Object> open(Map<?, ?> snapshot) {
        return eligible(snapshot) ? new GlobalsOverlay((IPersistentMap) snapshot) : new HashMap<>(snapshot);
    }

    /** INTERNAL caller attestation: called only for the actual newly frozen map,
     * derived from this machine. Never call with an unrelated persistent map.
     * Map views cannot add keys; all put/compute paths track unsupported keys.
     * This storage hint never substitutes for any checking/identity validation. */
    public static void rememberSnapshot(Map<?, ?> source, IPersistentMap frozen) {
        if (source instanceof GlobalsOverlay && ((GlobalsOverlay) source).canonicalKeys) remember(frozen, true);
    }

    /** Query before any Map view, so an unchanged freeze does no traversal. */
    public static IPersistentMap unchangedBase(Map<?, ?> source) {
        if (source instanceof GlobalsOverlay) {
            GlobalsOverlay globals = (GlobalsOverlay) source;
            if (globals.mutable == null) return globals.base;
        }
        return null;
    }

    private HashMap<Object, Object> materialize() {
        if (mutable == null) {
            HashMap<Object, Object> copy = new HashMap<>(baseMap);
            mutable = copy;
            // The eager table now owns its own key/value references. Do not
            // retain the old persistent table for a long-lived changed machine.
            base = null;
            baseMap = null;
        }
        return mutable;
    }
    private HashMap<Object, Object> forKey(Object key) {
        if (!canonicalKey(key)) canonicalKeys = false;
        return materialize();
    }

    @Override public Object get(Object key) {
        if (mutable != null) return mutable.get(key);
        if (!canonicalKey(key)) return materialize().get(key);
        IMapEntry entry = base.entryAt(key);
        return entry != null && Objects.equals(key, entry.key()) ? entry.val() : null;
    }
    @Override public boolean containsKey(Object key) {
        if (mutable != null) return mutable.containsKey(key);
        if (!canonicalKey(key)) return materialize().containsKey(key);
        IMapEntry entry = base.entryAt(key);
        return entry != null && Objects.equals(key, entry.key());
    }
    @Override public int size() { return mutable == null ? base.count() : mutable.size(); }
    @Override public Object getOrDefault(Object key, Object defaultValue) {
        Object value = get(key);
        return value != null || containsKey(key) ? value : defaultValue;
    }
    @Override public boolean containsValue(Object value) { return materialize().containsValue(value); }
    @Override public Object put(Object key, Object value) { return forKey(key).put(key, value); }
    @Override public Object remove(Object key) { return materialize().remove(key); }
    @Override public void clear() { materialize().clear(); }
    @Override public void putAll(Map<?, ?> map) {
        // A source Map can be weakly consistent: a separate keySet pre-scan
        // need not describe the entries HashMap.putAll subsequently observes.
        // Do not propagate eligibility from this bulk operation.
        canonicalKeys = false;
        materialize().putAll(map);
    }
    @Override public Set<Entry<Object, Object>> entrySet() { return materialize().entrySet(); }
    @Override public Set<Object> keySet() { return materialize().keySet(); }
    @Override public Collection<Object> values() { return materialize().values(); }
    @Override public void forEach(BiConsumer<? super Object, ? super Object> action) { materialize().forEach(action); }
    @Override public Object putIfAbsent(Object key, Object value) { return forKey(key).putIfAbsent(key, value); }
    @Override public boolean remove(Object key, Object value) { return materialize().remove(key, value); }
    @Override public Object replace(Object key, Object value) { return materialize().replace(key, value); }
    @Override public boolean replace(Object key, Object oldValue, Object newValue) { return materialize().replace(key, oldValue, newValue); }
    @Override public void replaceAll(BiFunction<? super Object, ? super Object, ?> function) { materialize().replaceAll(function); }
    @Override public Object computeIfAbsent(Object key, Function<? super Object, ?> function) { return forKey(key).computeIfAbsent(key, function); }
    @Override public Object computeIfPresent(Object key, BiFunction<? super Object, ? super Object, ?> function) { return forKey(key).computeIfPresent(key, function); }
    @Override public Object compute(Object key, BiFunction<? super Object, ? super Object, ?> function) { return forKey(key).compute(key, function); }
    @Override public Object merge(Object key, Object value, BiFunction<? super Object, ? super Object, ?> function) { return forKey(key).merge(key, value, function); }
}
