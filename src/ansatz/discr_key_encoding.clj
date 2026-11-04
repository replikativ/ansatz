(ns ansatz.discr-key-encoding
  "Wire policy for shared DiscrTree keys, separate from ConstantInfo store formats.
   Lean Meta/DiscrTree/Main.lean keys belong to the producing toolchain's .olean;
   independently persisted ansatz indices must retain that encoding explicitly."
  (:require [clojure.edn :as edn]))

(def write-version 2)
(def readable-versions #{1 2})

(defn encoding
  "Read an artifact's encoding. Missing metadata denotes the frozen legacy encoder."
  [artifact]
  (let [version (get artifact :key-encoding 1)]
    (when-not (contains? readable-versions version)
      (throw (ex-info "Unsupported discrimination key encoding; update ansatz or re-import the store"
                      {:kind :discr-key-encoding-error :found version :readable readable-versions})))
    version))

(defn entries
  "Validate/unwrap a persisted entry collection. Bare old sequences mean encoding 1."
  [artifact]
  (when (map? artifact)
    (when-not (contains? artifact :key-encoding)
      (throw (ex-info "Persisted key entries require an encoding"
                      {:kind :discr-key-encoding-error})))
    (encoding artifact))
  (let [rows (if (map? artifact) (:entries artifact) artifact)]
    (when-not (or (nil? artifact)
                  (and (sequential? rows)
                       (every? #(and (sequential? %) (= 2 (count %))
                                     (string? (first %)) (string? (second %))) rows)))
      (throw (ex-info "Malformed persisted key entries" {:kind :discr-key-encoding-error})))
    (or rows [])))

(defn entries-artifact [rows]
  {:key-encoding write-version :entries rows})

(defn read-path
  "Decode a catalogue datom or query envelope. Bare stored paths are encoding 1."
  [encoded]
  (let [artifact (if (string? encoded) (edn/read-string encoded) encoded)
        _ (when (and (map? artifact) (not (contains? artifact :key-encoding)))
            (throw (ex-info "Persisted key path requires an encoding" {:kind :discr-key-encoding-error})))
        version (encoding artifact)
        path (if (map? artifact) (:keys artifact) artifact)]
    (when-not (and (vector? path) (every? map? path))
      (throw (ex-info "Malformed persisted key path" {:kind :discr-key-encoding-error})))
    {:key-encoding version :keys path}))

(defn path-artifact [version path]
  (read-path {:key-encoding version :keys (vec path)}))

(defn stored-path
  "Carry the source artifact's version into a catalogue's independently durable datom."
  [version encoded]
  (let [source (if (string? encoded) (edn/read-string encoded) encoded)]
    (when (and (map? source) (not= version (encoding source)))
      (throw (ex-info "Key path and enclosing artifact encodings differ"
                      {:kind :discr-key-encoding-error :artifact version :path (encoding source)})))
    (pr-str (path-artifact version (:keys (read-path source))))))

(defn checked-query
  "Explicitly tagged queries must agree with the index. Raw paths are caller-supplied
   structural paths, interpreted in that index's encoding, never re-encoded implicitly."
  [version query]
  (encoding {:key-encoding version})
  (let [q (if (string? query) (edn/read-string query) query)]
    (when (and (map? q) (not= version (encoding q)))
      (throw (ex-info "Query and index key encodings differ"
                      {:kind :discr-key-encoding-error :query (encoding q) :index version})))
    (:keys (read-path q))))
