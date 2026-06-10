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
