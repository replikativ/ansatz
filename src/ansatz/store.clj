(ns ansatz.store
  "Durable, discoverable location for Ansatz kernel stores (PSS + konserve).

   WHY THIS EXISTS. A store is a persistent B-tree of declarations on disk. It MUST
   live in a durable directory. It must NOT live in `/tmp` (cleaned at 10 days) or
   `/var/tmp` (30 days): `systemd-tmpfiles` deletes files there by access time, which
   silently erodes a store one cold node at a time — a real incident that looked like
   index corruption but was the OS removing unaccessed `.ksv` files. Stores belong in
   an XDG-conformant *data* directory that nothing sweeps.

   RESOLUTION. The base directory holding all named stores (`data-root`), highest
   precedence first:
     1. $ANSATZ_STORE_DIR                              — explicit override (a dir of stores)
     2. $XDG_DATA_HOME/ansatz/stores                   — Linux / XDG
     3. ~/Library/Application Support/ansatz/stores    — macOS
     4. ~/.local/share/ansatz/stores                   — fallback

   A *named* store (e.g. \"mathlib\", \"cslib\", \"init\") lives at `<data-root>/<name>`.
   This is the one convention BOTH the build (setup scripts) and the load (`a/init!`,
   tests) share, so a library user only has to set `$ANSATZ_STORE_DIR` (or accept the
   default) for their dynamically-loaded Ansatz code to find the same stores the setup
   scripts wrote."
  (:require [clojure.java.io :as io]
            [clojure.edn :as edn]
            [clojure.pprint :as pprint]
            [clojure.string :as str]))

(defn- non-empty [s] (when (and s (not (str/blank? s))) s))

(defn- mac? []
  (str/starts-with? (str/lower-case (System/getProperty "os.name" "")) "mac"))

(defn data-root
  "Absolute base directory for all Ansatz stores (a *directory of stores*; not created).
   Resolution: $ANSATZ_STORE_DIR → $XDG_DATA_HOME/ansatz/stores → platform default."
  ^String []
  (or (non-empty (System/getenv "ANSATZ_STORE_DIR"))
      (when-let [xdg (non-empty (System/getenv "XDG_DATA_HOME"))]
        (.getPath (io/file xdg "ansatz" "stores")))
      (let [home (System/getProperty "user.home")]
        (.getPath (io/file home
                           (if (mac?) "Library/Application Support/ansatz/stores"
                               ".local/share/ansatz/stores"))))))

(defn store-dir
  "Absolute path of the named store under `data-root` (pure — no side effects, dir
   may not exist yet). Use this when BUILDING a store."
  ^String [store-name]
  (.getPath (io/file (data-root) (name store-name))))

(defn ensure-data-root!
  "Create `data-root` if absent and return it. Call before building a store there."
  ^String []
  (let [d (io/file (data-root))]
    (.mkdirs d)
    (.getPath d)))

(def ^:private legacy-roots
  "Pre-fix locations a store may still sit in. `/var/tmp/ansatz-<name>` was the old
   default and may hold an (eroding) store; we look there so existing setups keep
   working while we migrate."
  ["/var/tmp" "/tmp"])

(defn- non-empty-dir? [^java.io.File f]
  (and (.isDirectory f) (boolean (seq (.list f)))))

(defn resolve-existing
  "Path of an existing store named `store-name`, searching the durable `data-root`
   first, then the legacy `/var/tmp/ansatz-<name>` (and `/tmp`). Returns nil if none
   exists. A store 'exists' iff its directory is present and non-empty. Use this when
   LOADING — it tolerates both the new and legacy layouts."
  ^String [store-name]
  (let [nm (name store-name)
        candidates (cons (store-dir nm)
                         (for [r legacy-roots] (.getPath (io/file r (str "ansatz-" nm)))))]
    (some (fn [p] (when (non-empty-dir? (io/file p)) p)) candidates)))

;; ============================================================
;; Store format + manifest
;; ============================================================

(def write-format
  "Format emitted by this build. Format 2 preserves exact full-ConstantInfo hints,
   including regular zero and the entire UInt32 range."
  2)

(def readable-formats
  "Formats this build can decode. Reading format 1 retains its legacy full-CI
   interpretation; it cannot recover information an old writer discarded."
  #{1 2})

(def store-format
  "Compatibility alias for the writer format. Use readable-formats for readers."
  write-format)

(defn compatibility-errors
  "Pure comparison of manifest metadata with explicit consumer requirements.
   Supported requirements: :store/format, :branch, :artifact/cohort (exact),
   :provenance (required key/value subset), :store/capabilities (required subset).
   Metadata compatibility is not kernel verification or artifact authentication."
  [manifest requirements]
  (let [known #{:store/format :branch :artifact/cohort :provenance :store/capabilities}
        unknown (remove known (keys requirements))]
    (when (seq unknown)
      (throw (ex-info "Unknown store compatibility requirements" {:unknown (vec unknown)})))
    (into {}
          (keep (fn [[k expected]]
                  (let [found (get manifest k)
                        matches? (case k
                                   :provenance (and (map? found)
                                                    (every? (fn [[pk pv]]
                                                              (and (contains? found pk)
                                                                   (= pv (get found pk)))) expected))
                                   :store/capabilities (every? (set found) expected)
                                   (= expected found))]
                    (when-not matches? [k {:expected expected :found found}]))))
          requirements)))

(defn manifest-file ^java.io.File [store-path] (io/file store-path "manifest.edn"))

(defn read-manifest
  "The store's manifest map, or nil when there is none (an unfinished import, or a pre-format
   store)."
  [store-path]
  (let [f (manifest-file store-path)]
    (when (.exists f)
      (edn/read-string (slurp f)))))

(defn write-manifest!
  "Write the manifest LAST: it is what marks an import complete."
  [store-path m]
  (spit (manifest-file store-path)
        (with-out-str (pprint/pprint m))))

(defn check-format!
  "Return a readable store manifest, or reject an incomplete/unsupported store.
   This checks schema compatibility, not declaration validity or producer trust."
  [store-path]
  (let [m (read-manifest store-path)
        f (:store/format m)]
    (cond
      (nil? m)
      (throw (ex-info (str "No store manifest at " store-path
                           " — the import is incomplete or predates manifests. Re-import it.")
                      {:store store-path :readable readable-formats}))
      (not (contains? readable-formats f))
      (throw (ex-info (str "Store " store-path " is format " f ", this ansatz reads formats "
                           (sort readable-formats) ". Re-import with a supported writer or update ansatz.")
                      {:store store-path :found f :readable readable-formats}))
      :else m)))

(defn check-compatible!
  "Check readable format and consumer requirements before opening/installing a store."
  [store-path requirements]
  (let [m (check-format! store-path)
        errors (compatibility-errors m requirements)]
    (when (seq errors)
      (throw (ex-info "Store manifest does not match the requested artifacts"
                      {:store store-path :mismatches errors})))
    m))
