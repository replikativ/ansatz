// Ansatz kernel — Persistent (immutable) environment.

package ansatz.kernel;

import java.lang.ref.SoftReference;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Persistent kernel environment storing declarations.
 *
 * Design (following Lean 4's persistent data structures with shared cache):
 * - locals: Clojure PersistentHashMap — immutable, per-context additions
 * - sharedCache: ConcurrentHashMap<Name, SoftReference<ConstantInfo>> — GC-managed cache
 * - externalLookup: pure function to konserve/flatstore (read-only)
 * - visibilityCheck: optional staged-admission predicate checked before cache
 *
 * addConstant() returns a NEW Env (structural sharing via PersistentHashMap).
 * sharedCache uses SoftReferences so the JVM can reclaim cold declarations under
 * memory pressure. Re-fetching from the PSS/filestore is cheap (B-tree + LRU disk cache).
 * Fork is free — persistent map is already shared.
 */
public final class Env {

    // Locally added constants (immutable persistent map: Name → ConstantInfo)
    private final clojure.lang.IPersistentMap locals;

    // Shared cache for external lookups (SoftReference allows GC to reclaim under pressure)
    // Safe to share across forks: same Name → same ConstantInfo from external store
    private final ConcurrentHashMap<Name, SoftReference<ConstantInfo>> sharedCache;

    private final boolean quotEnabled;

    /**
     * Optional external lookup function for PSS-backed environments.
     * Pure: takes a Name, returns a ConstantInfo or null.
     */
    private final clojure.lang.IFn externalLookup;
    private final int externalSize;
    private final clojure.lang.IFn visibilityCheck;

    // Private constructor — use factory methods
    private Env(clojure.lang.IPersistentMap locals,
                ConcurrentHashMap<Name, SoftReference<ConstantInfo>> sharedCache,
                boolean quotEnabled,
                clojure.lang.IFn externalLookup,
                int externalSize,
                clojure.lang.IFn visibilityCheck) {
        this.locals = locals;
        this.sharedCache = sharedCache;
        this.quotEnabled = quotEnabled;
        this.externalLookup = externalLookup;
        this.externalSize = externalSize;
        this.visibilityCheck = visibilityCheck;
    }

    /** Create an empty environment (no external lookup). */
    public Env() {
        this(clojure.lang.PersistentHashMap.EMPTY,
             new ConcurrentHashMap<>(),
             false, null, 0, null);
    }

    /**
     * Set external lookup. Returns a NEW Env (immutable).
     */
    public Env withExternalLookup(clojure.lang.IFn lookupFn, int size) {
        return new Env(locals, sharedCache, quotEnabled, lookupFn, size, null);
    }

    /**
     * Set external lookup with an admission-order visibility predicate.
     *
     * The predicate is checked before the shared cache, so cached declarations
     * cannot bypass staged verification. Visible declarations are still cached,
     * matching Lean's in-memory environment and preserving pointer-stable
     * repeated lookups for IdentityHashMap-based kernel caches.
     */
    public Env withExternalLookupFiltered(clojure.lang.IFn lookupFn,
                                          int size,
                                          clojure.lang.IFn visibilityCheck) {
        return new Env(locals, sharedCache, quotEnabled, lookupFn, size, visibilityCheck);
    }

    /**
     * Set external lookup without the shared ConstantInfo cache.
     */
    public Env withExternalLookupUncached(clojure.lang.IFn lookupFn, int size) {
        return new Env(locals, null, quotEnabled, lookupFn, size, null);
    }

    public ConstantInfo lookup(Name name) {
        // 1. Check locals (immutable, per-context)
        Object local = locals.valAt(name);
        if (local != null) return (ConstantInfo) local;
        // Staged verification must reject not-yet-admitted constants even if
        // they were cached by a different view of the same environment.
        if (visibilityCheck != null && !truthy(visibilityCheck.invoke(name))) {
            return null;
        }
        // 2. Check shared cache — SoftReference may have been cleared under GC pressure
        if (sharedCache != null) {
            SoftReference<ConstantInfo> ref = sharedCache.get(name);
            if (ref != null) {
                ConstantInfo cached = ref.get();
                if (cached != null) return cached;
                // Ref was cleared — fall through to re-fetch
            }
        }
        // 3. External lookup + cache
        if (externalLookup != null) {
            Object result = externalLookup.invoke(name);
            if (result instanceof ConstantInfo) {
                ConstantInfo ext = (ConstantInfo) result;
                if (sharedCache != null) {
                    sharedCache.put(ext.name, new SoftReference<>(ext));
                }
                return ext;
            }
        }
        return null;
    }

    public ConstantInfo lookupOrThrow(Name name) {
        ConstantInfo ci = lookup(name);
        if (ci == null) {
            throw new RuntimeException("Unknown constant: " + name);
        }
        return ci;
    }

    /**
     * Add a constant. Returns a NEW Env with the constant added.
     * The original Env is unchanged (persistent/immutable).
     */
    public Env addConstant(ConstantInfo ci) {
        if (lookup(ci.name) != null) {
            throw new RuntimeException("Constant already declared: " + ci.name);
        }
        return new Env(locals.assoc(ci.name, ci), sharedCache,
                      quotEnabled, externalLookup, externalSize, visibilityCheck);
    }

    /**
     * Like addConstant, but REPLACES an existing constant of the same name instead of throwing.
     * For SURFACE redefinition (a/defn / a/theorem in a REPL, matching Clojure `defn` semantics).
     * Kernel proof / install paths keep using the strict {@link #addConstant}.
     */
    public Env addOrReplaceConstant(ConstantInfo ci) {
        return new Env(locals.assoc(ci.name, ci), sharedCache,
                      quotEnabled, externalLookup, externalSize, visibilityCheck);
    }

    /** Returns a NEW Env with quot enabled. */
    public Env enableQuot() {
        if (quotEnabled) return this;
        return new Env(locals, sharedCache, true, externalLookup, externalSize, visibilityCheck);
    }

    public boolean isQuotEnabled() {
        return quotEnabled;
    }

    public int size() {
        if (externalLookup != null) {
            return Math.max(locals.count(), externalSize);
        }
        return locals.count();
    }

    /**
     * Return all constants currently in locals + shared cache.
     * For non-PSS envs, this is all declarations.
     */
    public java.util.Collection<ConstantInfo> allConstants() {
        java.util.ArrayList<ConstantInfo> result = new java.util.ArrayList<>();
        // Add all locals
        for (Object entry : locals) {
            clojure.lang.MapEntry me = (clojure.lang.MapEntry) entry;
            result.add((ConstantInfo) me.val());
        }
        return result;
    }

    /**
     * Fork is a no-op for immutable Env — the persistent map is already shared.
     * Returns a new Env with the same locals (via structural sharing) and
     * the same shared cache. Additions to the fork don't affect the original.
     */
    public Env fork() {
        // Already immutable — just return this.
        // The caller can addConstant() which returns a new Env.
        return this;
    }

    private static boolean truthy(Object value) {
        return value != null && !Boolean.FALSE.equals(value);
    }
}
