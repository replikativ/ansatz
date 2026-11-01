(ns prototype.declaration-store
  "Experimental content-addressed declarations and immutable index checkpoints.
  Reopening reads the index; only selected declaration blobs are read/decoded."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.walk :as walk]
            [prototype.import-ir :as ir]
            [prototype.machine :as m])
  (:import [java.nio.charset StandardCharsets]
           [java.io BufferedWriter OutputStreamWriter PushbackReader]
           [java.nio.file Files CopyOption StandardCopyOption FileAlreadyExistsException]
           [java.security MessageDigest DigestOutputStream DigestInputStream]))

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

(defn- verify-file! [file expected]
  (let [md (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
    (with-open [input (DigestInputStream. (io/input-stream file) md)]
      (loop [] (when-not (= -1 (.read input buffer)) (recur))))
    (when-not (= expected (.formatHex (java.util.HexFormat/of) (.digest md)))
      (m/fail "Store digest mismatch" {:file (str file) :digest expected}))))

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

(defn overlay
  "Combine raw or indexed catalogues without reading declaration blobs.
  Resolves only the requested name. Duplicate rows are reconciled when read,
  so source-local metadata can win without hiding actual artifact drift.
  Returns a read-only catalogue, not a store supporting durable publication."
  [base overlay-catalogue]
  (let [base-declarations (:declarations base)
        overlay-declarations (:declarations overlay-catalogue)
        read-row (fn [catalogue name]
                   (if-let [read-declaration (:read-declaration catalogue)]
                     (read-declaration name)
                     (get-in catalogue [:declarations name])))]
    (let [redirects (reduce-kv
                     (fn [out symbol redirect]
                       (when-let [old (get out symbol)]
                         (when-not (= old redirect)
                           (m/fail "Conflicting consumer redirect overlay" {:symbol symbol})))
                       (assoc out symbol redirect))
                     (or (:prototype.runtime-abi/consumer-redirects base) {})
                     (or (:prototype.runtime-abi/consumer-redirects overlay-catalogue) {}))]
    {:prototype.runtime-abi/consumer-redirects redirects
     :manifests (into (vec (:manifests base)) (:manifests overlay-catalogue))
     :declarations (merge base-declarations overlay-declarations)
     :read-declaration
     (fn [name]
       (let [base? (contains? base-declarations name)
             overlay? (contains? overlay-declarations name)]
         (cond
           (and base? overlay?)
           (ir/reconcile-declarations (read-row base name) (read-row overlay-catalogue name))
           overlay? (read-row overlay-catalogue name)
           base? (read-row base name)
           :else nil)))})))

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
  (when (seq (:prototype.runtime-abi/consumer-redirects store))
    (m/fail "Consumer redirects are host configuration, not a writable producer store" {}))
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
              (let [row (if (contains? (:declarations store) (:name row))
                          (ir/reconcile-declarations ((:read-declaration store) (:name row)) row) row)]
                (with-declaration! store row)))) store (rest lines)))))
   (empty-store root) paths))

(defn checkpoint!
  "Publish immutable index metadata; return its content hash. This full index
  checkpoint is separate from incremental in-memory declaration-map edits."
  [store]
  (when (seq (:prototype.runtime-abi/consumer-redirects store))
    (m/fail "Reconstruct consumer redirects from authenticated host configuration after restore" {}))
  ;; Stream the same canonical bytes as publish!, without postwalking the whole
  ;; index and retaining its transformed tree, String and UTF-8 byte array.
  (let [dir (io/file (:root store) "indexes")
        _ (.mkdirs dir)
        tmp (Files/createTempFile (.toPath dir) "publish-" ".json"
                                  (make-array java.nio.file.attribute.FileAttribute 0))
        md (MessageDigest/getInstance "SHA-256")]
    (try
      (with-open [out (DigestOutputStream. (io/output-stream (.toFile tmp)) md)
                  writer (BufferedWriter. (OutputStreamWriter. out StandardCharsets/UTF_8))]
        (.write writer "{\"declarations\":[")
        (let [entries (sort-by first (map (fn [[name hash]] [(encode name) hash]) (:declarations store)))]
          (doseq [[i [name hash]] (map-indexed vector entries)]
            (when (pos? i) (.write writer ","))
            (.write writer "[") (.write writer ^String name)
            (.write writer ",\"") (.write writer ^String (valid-hash! hash)) (.write writer "\"]")))
        (.write writer "],\"manifests\":[")
        (doseq [[i manifest] (map-indexed vector (:manifests store))]
          (when (pos? i) (.write writer ","))
          (.write writer ^String (encode manifest)))
        (.write writer "],\"schema\":")
        (.write writer ^String (encode "lean-ir-store/1"))
        (.write writer "}"))
      (let [hash (.formatHex (java.util.HexFormat/of) (.digest md))
            file (path (:root store) "indexes" hash)
            verify! (fn []
                      (let [existing (MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
                        (with-open [input (DigestInputStream. (io/input-stream file) existing)]
                          (loop [] (when-not (= -1 (.read input buffer)) (recur))))
                        (when-not (= hash (.formatHex (java.util.HexFormat/of) (.digest existing)))
                          (m/fail "Store digest mismatch" {:file (str file) :digest hash}))))]
        (if (.exists file) (verify!)
          (try (Files/move tmp (.toPath file) (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE]))
               (catch FileAlreadyExistsException _ (verify!))))
        hash)
      (finally (Files/deleteIfExists tmp)))))

(defn- next-character [^PushbackReader reader]
  (loop [c (.read reader)]
    (if (contains? #{9 10 13 32} c) (recur (.read reader)) c)))

(defn- expect-character! [reader expected]
  (when-not (= (int expected) (next-character reader))
    (m/fail "Malformed store index JSON" {})))

(defn- intern-name [^java.util.HashMap names name]
  ;; Prefix sharing is an implementation detail of the reopened index. Numeric
  ;; and string Name components remain distinct; no serialized bytes change.
  (loop [current name parts []]
    (cond
      (= ["anonymous"] current)
      (reduce (fn [prefix [kind payload]]
                (let [candidate [kind prefix payload]]
                  (or (.get names candidate)
                      (do (.put names candidate candidate) candidate))))
              ["anonymous"] (rseq parts))
      (and (vector? current) (= 3 (count current))
           (contains? #{"str" "num"} (first current)))
      (recur (second current) (conj parts [(first current) (nth current 2)]))
      :else name)))

(defn- read-index-entries [^PushbackReader reader]
  (expect-character! reader \[)
  (let [names (java.util.HashMap.)]
    (loop [entries (transient {})]
      (let [c (next-character reader)]
        (if (= (int \]) c) (persistent! entries)
          (do
            (.unread reader c)
            (let [entry (json/read reader :key-fn keyword :bigdec false)]
              (when-not (and (vector? entry) (= 2 (count entry)) (vector? (first entry)))
                (m/fail "Unsupported store index" {}))
              (let [[name hash] entry name (intern-name names name)]
                (valid-hash! hash)
                (when-not (= ::absent (get entries name ::absent))
                  (m/fail "Duplicate store declaration name" {}))
                (let [entries (assoc! entries name hash) separator (next-character reader)]
                  (case separator
                    44 (do (when (= (int \]) (let [c (next-character reader)] (.unread reader c) c))
                             (m/fail "Malformed store index JSON" {}))
                           (recur entries))
                    93 (persistent! entries)
                    (m/fail "Malformed store index JSON" {})))))))))))

(defn open-index
  "Read and validate an immutable index without reading any declaration blobs."
  [root hash]
  (let [file (path root "indexes" hash)
        _ (verify-file! file hash)
        index (with-open [reader (PushbackReader. (io/reader file :encoding "UTF-8") 64)]
                (expect-character! reader \{)
                (loop [index {}]
                  (let [c (next-character reader)]
                    (if (= (int \}) c)
                      (if (empty? index) index (m/fail "Malformed store index JSON" {}))
                      (do (.unread reader c)
                        (let [key (json/read reader)
                              _ (when-not (string? key) (m/fail "Malformed store index JSON" {}))
                              key (keyword key)
                              _ (when (contains? index key) (m/fail "Duplicate store index field" {:field key}))
                              _ (expect-character! reader \:)
                              value (if (= :declarations key) (read-index-entries reader)
                                      (json/read reader :key-fn keyword :bigdec false))
                              index (assoc index key value)
                              separator (next-character reader)]
                          (case separator
                            44 (recur index)
                            125 (do (when-not (= -1 (next-character reader))
                                      (m/fail "Trailing store index JSON" {})) index)
                            (m/fail "Malformed store index JSON" {}))))))))]
    (when-not (and (= "lean-ir-store/1" (:schema index))
                   (vector? (:manifests index)) (map? (:declarations index)))
      (m/fail "Unsupported store index" {}))
    (doseq [manifest (:manifests index)] (ir/validate-manifest! manifest))
    (catalogue root (:declarations index) (:manifests index)
               (atom {:blob-reads 0 :blob-bytes 0 :blob-publishes 0
                      :index-reads 1 :index-bytes (Files/size (.toPath file))}))))

(defn open-index-verified-stream
  "Authenticate exactly the streamed index bytes being parsed. No declaration
   bodies retained/read until requested. Existing open-index API is unchanged."
  [root hash]
  (let [file (path root "indexes" hash)
        digest (MessageDigest/getInstance "SHA-256")
        index (with-open [input (DigestInputStream. (io/input-stream file) digest)
                          reader (PushbackReader.
                                   (java.io.InputStreamReader. input
                                     (doto (.newDecoder StandardCharsets/UTF_8)
                                       (.onMalformedInput java.nio.charset.CodingErrorAction/REPORT)
                                       (.onUnmappableCharacter java.nio.charset.CodingErrorAction/REPORT))) 64)]
                (expect-character! reader \{)
                (loop [index {}]
                  (let [c (next-character reader)]
                    (if (= (int \}) c)
                      (if (empty? index) index (m/fail "Malformed store index JSON" {}))
                      (do (.unread reader c)
                        (let [key (json/read reader)
                              _ (when-not (string? key) (m/fail "Malformed store index JSON" {}))
                              key (keyword key)
                              _ (when (contains? index key) (m/fail "Duplicate store index field" {:field key}))
                              _ (expect-character! reader \:)
                              value (if (= :declarations key) (read-index-entries reader)
                                      (json/read reader :key-fn keyword :bigdec false))
                              index (assoc index key value)
                              separator (next-character reader)]
                          (case separator
                            44 (recur index)
                            125 (do (when-not (= -1 (next-character reader))
                                      (m/fail "Trailing store index JSON" {})) index)
                            (m/fail "Malformed store index JSON" {}))))))))]
    (when-not (= hash (.formatHex (java.util.HexFormat/of) (.digest digest)))
      (m/fail "Store digest mismatch" {:file (str file) :digest hash}))
    (when-not (and (= "lean-ir-store/1" (:schema index))
                   (vector? (:manifests index)) (map? (:declarations index)))
      (m/fail "Unsupported store index" {}))
    (doseq [manifest (:manifests index)] (ir/validate-manifest! manifest))
    (catalogue root (:declarations index) (:manifests index)
               (atom {:blob-reads 0 :blob-bytes 0 :blob-publishes 0
                      :index-reads 1 :index-bytes (Files/size (.toPath file))}))))
