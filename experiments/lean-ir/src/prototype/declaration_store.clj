(ns prototype.declaration-store
  "Experimental content-addressed declarations and immutable index checkpoints.
  Reopening reads the index; only selected declaration blobs are read/decoded."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.walk :as walk]
            [prototype.import-ir :as ir]
            [prototype.machine :as m])
  (:import [java.nio.charset StandardCharsets]
           [java.nio.file Files CopyOption StandardCopyOption FileAlreadyExistsException]
           [java.security MessageDigest]))

(defn- encode [x]
  ;; Map order does not affect identity; vector order and numeric/string name
  ;; components do. Hashes identify serialization bytes, not semantic equivalence.
  (json/write-str
   (walk/postwalk
    #(if (map? %) (into (sorted-map-by (fn [a b] (compare (str a) (str b)))) %) %) x)))

(defn- utf8-bytes [text] (.getBytes ^String text StandardCharsets/UTF_8))
(defn- digest [data]
  (.formatHex (java.util.HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") ^bytes data)))

(defn- valid-hash! [hash]
  (when-not (and (string? hash) (re-matches #"[0-9a-f]{64}" hash))
    (m/fail "Invalid store digest" {:digest hash}))
  hash)

(defn- path [root kind hash]
  (io/file root kind (str (valid-hash! hash) ".json")))

(defn- read-data [file expected]
  (let [data (Files/readAllBytes (.toPath (io/file file)))]
    (when-not (= expected (digest data))
      (m/fail "Store digest mismatch" {:file (str file) :digest expected}))
    data))

(defn- decode [data]
  (json/read-str (String. ^bytes data StandardCharsets/UTF_8) :key-fn keyword :bigdec false))

(defn- publish! [root kind value]
  (let [data (utf8-bytes (encode value)) hash (digest data) file (path root kind hash)
        dir (.getParentFile file)]
    (.mkdirs dir)
    (if (.exists file)
      (read-data file hash)
      (let [tmp (Files/createTempFile (.toPath dir) "publish-" ".json"
                                      (make-array java.nio.file.attribute.FileAttribute 0))]
        (try
          (Files/write tmp data (make-array java.nio.file.OpenOption 0))
          (try (Files/move tmp (.toPath file) (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE]))
               (catch FileAlreadyExistsException _ (read-data file hash)))
          (finally (Files/deleteIfExists tmp)))))
    {:hash hash :bytes (alength data)}))

(defn stats [store] @(:io-stats store))

(defn- catalogue [root declarations manifests counters]
  (let [root (.getCanonicalPath (io/file root))]
    {:root root
     :declarations declarations :manifests manifests :io-stats counters
     :read-declaration
     (fn [name]
       (when-let [hash (get declarations name)]
         (let [data (read-data (path root "declarations" hash) hash)
               row (decode data)]
           (swap! counters #(-> % (update :blob-reads inc) (update :blob-bytes + (alength data))))
           (when-not (= name (:name row))
             (m/fail "Store declaration name mismatch" {:name name :actual (:name row)}))
           row)))}))

(defn empty-store [root]
  (catalogue root {} [] (atom {:blob-reads 0 :blob-bytes 0 :blob-publishes 0 :index-reads 0 :index-bytes 0})))

(defn with-declaration!
  "Publish one row and return a new catalogue. Old catalogues keep old hashes.
  Counters are shared across these versions; no full index is written here."
  [store row]
  (when-not (and (= "decl" (:kind row)) (vector? (:name row)))
    (m/fail "Invalid store declaration" {:row row}))
  (let [{:keys [hash]} (publish! (:root store) "declarations" row)]
    (swap! (:io-stats store) update :blob-publishes inc)
    (catalogue (:root store) (assoc (:declarations store) (:name row) hash)
               (:manifests store) (:io-stats store))))

(defn pack!
  "One-time streaming conversion of JSONL bundles. Still decodes every input
  declaration at pack time; selected reloads subsequently avoid that work."
  [root paths]
  (reduce
   (fn [store input]
     (with-open [reader (io/reader input)]
       (let [lines (line-seq reader)
             manifest (ir/validate-manifest! (json/read-str (or (first lines) "null") :key-fn keyword))
             store (catalogue (:root store) (:declarations store) (conj (:manifests store) manifest) (:io-stats store))]
         (reduce
          (fn [store line]
            (let [row (json/read-str line :key-fn keyword :bigdec false)]
              (when (contains? (:declarations store) (:name row))
                (let [old ((:read-declaration store) (:name row))]
                  (when-not (= (select-keys old [:kind :ir :dependencies])
                               (select-keys row [:kind :ir :dependencies]))
                    (m/fail "Conflicting declaration" {:name (:name row)}))))
              (with-declaration! store row))) store (rest lines)))))
   (empty-store root) paths))

(defn checkpoint!
  "Publish immutable index metadata; return its content hash. Explicit O(N)
  checkpoint, separate from O(log N) in-memory declaration-map edits."
  [store]
  (:hash (publish! (:root store) "indexes"
                   {:schema "lean-ir-store/1" :manifests (:manifests store)
                    :declarations (sort-by (comp encode first) (:declarations store))})))

(defn open-index
  "Read and validate an immutable index without reading any declaration blobs."
  [root hash]
  (let [data (read-data (path root "indexes" hash) hash)
        index (decode data)
        entries (:declarations index)]
    (when-not (and (= "lean-ir-store/1" (:schema index))
                   (vector? (:manifests index))
                   (vector? entries)
                   (every? #(and (vector? %) (= 2 (count %)) (vector? (first %))) entries))
      (m/fail "Unsupported store index" {:index index}))
    (doseq [manifest (:manifests index)] (ir/validate-manifest! manifest))
    (doseq [[_ digest] entries] (valid-hash! digest))
    (when-not (= (count entries) (count (into {} entries)))
      (m/fail "Duplicate store declaration name" {}))
    (catalogue root (into {} entries) (:manifests index)
               (atom {:blob-reads 0 :blob-bytes 0 :blob-publishes 0
                      :index-reads 1 :index-bytes (alength data)}))))
