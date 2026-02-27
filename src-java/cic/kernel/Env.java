// Copyright (c) 2026 Simmis GmbH. All rights reserved.
// CIC kernel — Mutable environment.

package cic.kernel;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Mutable kernel environment storing declarations.
 * Uses LinkedHashMap with LRU eviction when PSS-backed external lookup is set,
 * so that only recently accessed declarations stay in memory.
 * Without external lookup, behaves as an unbounded cache (same as before).
 */
public final class Env {

    private static final int CACHE_MAX = 2048;

    private final LinkedHashMap<Name, ConstantInfo> constants =
        new LinkedHashMap<>(CACHE_MAX, 0.75f, true) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<Name, ConstantInfo> eldest) {
                if (externalLookup != null && size() > CACHE_MAX) {
                    eldest.getValue().value = null;  // drop value Expr tree early
                    return true;
                }
                return false;
            }
        };

    private boolean quotEnabled;

    /**
     * Optional external lookup function for PSS-backed environments.
     * When set, lookup checks this function if the HashMap misses.
     * This allows lazy loading from persistent storage without eagerly
     * deserializing all declarations.
     *
     * The function takes a Name and returns a ConstantInfo or null.
     */
    private clojure.lang.IFn externalLookup;
    private int externalSize;

    public Env() {
        this.quotEnabled = false;
    }

    /**
     * Set an external lookup function for lazy PSS-backed loading.
     * The function receives a Name and should return ConstantInfo or nil.
     */
    public void setExternalLookup(clojure.lang.IFn lookupFn, int size) {
        this.externalLookup = lookupFn;
        this.externalSize = size;
    }

    public ConstantInfo lookup(Name name) {
        ConstantInfo ci = constants.get(name);
        if (ci != null) return ci;
        if (externalLookup != null) {
            Object result = externalLookup.invoke(name);
            if (result instanceof ConstantInfo) {
                ConstantInfo ext = (ConstantInfo) result;
                // Cache locally for subsequent lookups (LRU will evict if full)
                constants.putIfAbsent(ext.name, ext);
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

    public void addConstant(ConstantInfo ci) {
        if (externalLookup != null) {
            // PSS already has this declaration; just cache in LRU
            constants.put(ci.name, ci);
            return;
        }
        ConstantInfo existing = constants.put(ci.name, ci);
        if (existing != null) {
            // Restore and throw
            constants.put(ci.name, existing);
            throw new RuntimeException("Constant already declared: " + ci.name);
        }
    }

    /**
     * Add constant, ignoring duplicates (for replay error recovery).
     */
    public void addConstantIfAbsent(ConstantInfo ci) {
        constants.putIfAbsent(ci.name, ci);
    }

    public void enableQuot() {
        this.quotEnabled = true;
    }

    public boolean isQuotEnabled() {
        return quotEnabled;
    }

    public int size() {
        if (externalLookup != null) {
            return Math.max(constants.size(), externalSize);
        }
        return constants.size();
    }
}
