(ns ansatz.store.fetch
  "Downloading a prebuilt store, so that using Mathlib from Clojure is a dependency and not a
   build.

   A store is published once per IMPORT, not per ansatz release: its identity is the library
   tag, the store format and a revision of our own import — `mathlib-v4.33.1-f1`. An INDEX
   (`stores.edn`) maps a store name and the format an ansatz build reads to the current id;
   ansatz reads the index at fetch time, so a new import reaches existing users without a new
   ansatz release. The index bundled in the jar is the offline fallback, never the authority.

   The artifacts are `.tar.gz` parts plus a `store.edn` descriptor carrying each part's
   sha256; a download resumes with a Range request, every part is verified before it is
   unpacked, and the store appears at its final path by an atomic rename — an interrupted
   fetch leaves nothing that `resolve-existing` would find.

   JDK only (`java.net.http`, `java.util.zip`): no HTTP or archive dependency enters the
   library. Set `ANSATZ_OFFLINE=1` to refuse fetching, `ANSATZ_STORE_INDEX` to point at
   another index (a file path or a URL), `ANSATZ_STORE_BASE` to mirror the artifacts
   elsewhere."
  (:require [ansatz.store :as store]
            [ansatz.store.archive :as archive]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.net URI]
           [java.net.http HttpClient HttpClient$Redirect HttpRequest HttpResponse$BodyHandlers]
           [java.nio.file Files]
           [java.security MessageDigest]
           [java.time Duration]))

(def default-index-url
  "The published index. A file in the store repository, not a release asset, so that
   publishing a new import is one commit there and reaches every ansatz build that reads the
   format it names."
  "https://raw.githubusercontent.com/replikativ/ansatz-stores/main/stores.edn")

(def bundled-index-resource "ansatz/stores.edn")

(defn- env [k] (let [v (System/getenv k)] (when-not (str/blank? v) v)))

(defn- offline? [] (boolean (env "ANSATZ_OFFLINE")))

(defn- client ^HttpClient []
  (-> (HttpClient/newBuilder)
      (.followRedirects HttpClient$Redirect/ALWAYS)         ; release downloads redirect to a CDN
      (.connectTimeout (Duration/ofSeconds 30))
      (.build)))

(defn- get-string [url]
  (let [req (-> (HttpRequest/newBuilder (URI/create url)) (.timeout (Duration/ofSeconds 60)) (.GET) (.build))
        resp (.send (client) req (HttpResponse$BodyHandlers/ofString))]
    (when-not (= 200 (.statusCode resp))
      (throw (ex-info (str "index request failed: HTTP " (.statusCode resp)) {:url url :status (.statusCode resp)})))
    (.body resp)))

(defn read-index
  "The store index: `ANSATZ_STORE_INDEX` (a path or a URL) if set, else the published index,
   else — offline, or the network failed — the copy bundled in the jar. Returns the index map
   with `:index/source` saying which it was."
  []
  (let [override (env "ANSATZ_STORE_INDEX")
        bundled (fn [] (when-let [r (io/resource bundled-index-resource)]
                         (assoc (edn/read-string (slurp r)) :index/source :bundled)))]
    (or (when override
          (let [s (if (re-find #"^https?://" override) (get-string override) (slurp override))]
            (assoc (edn/read-string s) :index/source override)))
        (when-not (offline?)
          (try (assoc (edn/read-string (get-string default-index-url)) :index/source default-index-url)
               (catch Exception _ nil)))
        (bundled)
        (throw (ex-info "no store index available (no network and none bundled)" {})))))

(defn entry
  "The index entry for `store-name` at the store format this build reads, or nil."
  [index store-name]
  (get-in index [:stores (name store-name) store/store-format]))

(defn- sha256-hex [^java.io.File f]
  (let [md (MessageDigest/getInstance "SHA-256")
        buf (byte-array (* 1024 1024))]
    (with-open [in (io/input-stream f)]
      (loop []
        (let [r (.read in buf)]
          (when (pos? r) (.update md buf 0 r) (recur)))))
    (apply str (map #(format "%02x" %) (.digest md)))))

(defn- human [bytes]
  (let [b (double bytes)]
    (cond (> b 1073741824) (format "%.2f GiB" (/ b 1073741824))
          (> b 1048576) (format "%.1f MiB" (/ b 1048576))
          :else (format "%d B" (long bytes)))))

(defn- download-part-from! [url dest have {:keys [sha256 size verbose?]}]
  (let [dest (io/file dest)]
    (let [req (cond-> (HttpRequest/newBuilder (URI/create url))
                (pos? have) (.header "Range" (str "bytes=" have "-"))
                true (.timeout (Duration/ofMinutes 60))
                true (.GET)
                true (.build))
          resp (.send (client) req (HttpResponse$BodyHandlers/ofInputStream))
          status (.statusCode resp)
          resume? (= 206 status)]
      (when-not (#{200 206} status)
        (throw (ex-info (str "download failed: HTTP " status) {:url url :status status})))
      (when (and (pos? have) (not resume?))
        (when verbose? (println "   server ignored Range; restarting" (.getName dest))))
      (with-open [in (.body resp)
                  out (io/output-stream dest :append resume?)]
        (let [buf (byte-array (* 1024 1024))
              t0 (System/nanoTime)]
          (loop [done (if resume? have 0) tick 0]
            (let [r (.read in buf)]
              (if (neg? r)
                (when verbose?
                  (println (format "   %s %s in %.0f s" (.getName dest) (human done)
                                   (/ (- (System/nanoTime) t0) 1e9))))
                (do (.write out buf 0 r)
                    (let [done (+ done r)
                          tick (if (and verbose? (> (- done tick) (* 64 1024 1024)))
                                 (do (print (format "\r   %s %s%s" (.getName dest) (human done)
                                                    (if size (format " / %s" (human size)) "")))
                                     (flush)
                                     done)
                                 tick)]
                      (recur done tick))))))))
      (when verbose? (print "\r") (flush))
      ;; A transfer that stopped short keeps what it got — the next call resumes from there.
      ;; Only a part that arrived in full and hashes wrong is corrupt, and that one goes.
      (when (and size (< (.length dest) (long size)))
        (throw (ex-info (str "download incomplete (" (.length dest) " of " size " bytes) — run it again to resume")
                        {:url url :have (.length dest) :size size})))
      (when (and sha256 (not= sha256 (sha256-hex dest)))
        (.delete dest)
        (throw (ex-info "checksum mismatch — the download was corrupted, try again"
                        {:url url :expected sha256})))
      dest)))

(defn- download-part!
  "Fetch `url` to `dest`, resuming when a partial file is there, and verify `sha256`.
   Returns dest."
  [url dest {:keys [sha256 size verbose?]}]
  (let [dest (io/file dest)
        have (if (.exists dest) (.length dest) 0)]
    (if (and size (= have size) sha256 (= sha256 (sha256-hex dest)))
      (do (when verbose? (println "   have" (.getName dest))) dest)
      (download-part-from! url dest have {:sha256 sha256 :size size :verbose? verbose?}))))

(defn fetch!
  "Download and install the store named `store-name` into the data root, and return its path.
   Refuses to overwrite an existing store. Options: `:index` (an index map, else read),
   `:base` (artifact base URL, else `ANSATZ_STORE_BASE` or the index's), `:verbose?`."
  [store-name & {:keys [index base verbose?] :or {verbose? true}}]
  (when (offline?)
    (throw (ex-info (str "ANSATZ_OFFLINE is set and there is no store named '" (name store-name) "'")
                    {:store store-name})))
  (let [nm (name store-name)
        dest (store/store-dir nm)
        _ (when (.exists (io/file dest))
            (throw (ex-info (str "a store already exists at " dest) {:store nm :path dest})))
        index (or index (read-index))
        e (or (entry index nm)
              (throw (ex-info (str "no published store named '" nm "' for store format "
                                   store/store-format " in the index (" (:index/source index) ")")
                              {:store nm :format store/store-format
                               :available (keys (:stores index))})))
        base (or base (env "ANSATZ_STORE_BASE") (:base e) (:base index))
        id (:id e)
        parts (:parts e)
        total (reduce + 0 (keep :size parts))
        work (io/file (store/ensure-data-root!) (str "." nm ".fetch"))
        staging (io/file work id)]
    (when-not (and base id (seq parts))
      (throw (ex-info "index entry is incomplete" {:entry e})))
    (when verbose?
      (println (str "Fetching store '" nm "' (" id ")" (when (pos? total) (str ", " (human total) " to download"))))
      (println (str "   from " base "/" id))
      (println (str "   into " dest)))
    (.mkdirs staging)
    (doseq [{:keys [file] :as p} parts]
      (let [f (io/file staging file)]
        (download-part! (str base "/" id "/" file) f (assoc p :verbose? verbose?))))
    (let [incoming (io/file work "store")]
      (when (.exists incoming)
        (run! io/delete-file (reverse (file-seq incoming))))
      (doseq [{:keys [file]} parts]
        (when verbose? (println "   unpacking" file))
        (archive/unpack! (io/file staging file) incoming))
      ;; the manifest must be there and readable by this build before anything is moved
      (store/check-format! (str incoming))
      (archive/move-into-place! incoming dest)
      (run! io/delete-file (reverse (file-seq staging)))
      (when verbose?
        (let [m (store/read-manifest dest)]
          (println (str "Store '" nm "' ready at " dest
                        (when-let [t (get-in m [:provenance :library/tag])] (str " (" t ")"))))))
      dest)))

(defn ensure-store!
  "The path of the store named `store-name`, fetching it when it is absent. This is what
   `(a/init! \"mathlib\")` calls: a user adds the dependency, asks for Mathlib, and gets it."
  [store-name & opts]
  (or (store/resolve-existing store-name)
      (apply fetch! store-name opts)))
