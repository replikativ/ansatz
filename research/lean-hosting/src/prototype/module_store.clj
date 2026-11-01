(ns prototype.module-store
  "Verified, disk-backed immutable native DAG. A complete validation pass precedes
   publication. Each uncached lookup verifies the indexed line SHA256 again, so
   later file mutation cannot silently change a snapshot's objects. Cache entries
   contain immutable nodes only and are shared safely between world forks."
  (:refer-clojure :exclude [load-file])
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.machine :as m]
            [prototype.module-data :as data]
            [prototype.native-heap :as heap]
            [prototype.native-scalar :as native])
  (:import [java.io BufferedReader InputStreamReader BufferedOutputStream DataOutputStream RandomAccessFile]
           [java.nio ByteBuffer]
           [java.nio.channels FileChannel]
           [java.nio.file Files StandardCopyOption]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.security MessageDigest DigestInputStream]
           [java.util Arrays LinkedHashMap]))

(defn- sha [bytes] (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes))
(defn- hex [bytes] (apply str (map #(format "%02x" (bit-and 255 %)) bytes)))
(defn- ascii-bytes? [value]
  (and (bytes? value)
       (let [^bytes bytes value]
         (loop [i 0]
           (if (< i (alength bytes))
             (if (neg? (aget bytes i)) false (recur (inc i)))
             true)))))
(defn- parse [bytes]
  ;; ASCII has the same characters in UTF8 and Latin1. Keep strict UTF8
  ;; decoding for every other input, including malformed byte sequences.
  (if (ascii-bytes? bytes)
    (json/read-str (String. ^bytes bytes StandardCharsets/ISO_8859_1) :key-fn keyword)
    (let [decoder (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))]
    (json/read-str (str (.decode decoder (ByteBuffer/wrap bytes))) :key-fn keyword))))
(defn- line! [^BufferedReader in maximum]
  (when-let [line (.readLine in)]
    (let [bytes (.getBytes ^String line StandardCharsets/UTF_8)]
      (when (> (alength bytes) maximum) (m/fail "ModuleData JSONL row limit exceeded" {}))
      bytes)))

(defn- read-at! [^FileChannel channel offset length]
  (let [buffer (ByteBuffer/allocate length)]
    (loop [position offset]
      (when (.hasRemaining buffer)
        (let [n (.read channel buffer (long position))]
          (when (<= n 0) (m/fail "Truncated ModuleData backing file" {:offset position}))
          (recur (+ position n)))))
    (.array buffer)))

(deftype Store [base size manifest digest ^FileChannel channel ^RandomAccessFile index cache cache-limit maximum-bytes closed]
  clojure.lang.ILookup
  (valAt [this key] (.valAt this key nil))
  (valAt [_ key not-found]
    (case key :base base :size size :manifest manifest :digest digest
          :channel channel :index index :cache cache :cache-limit cache-limit
          :maximum-bytes maximum-bytes :closed closed not-found))
  heap/NativeSource
  (contains-id? [_ id] (and (integer? id) (<= base id) (< id (+ base size))))
  (lookup-node [this id]
    (when (heap/contains-id? this id)
      (when @closed (m/fail "ModuleData source is closed" {}))
      (locking cache
        (or (.get ^LinkedHashMap cache id)
            (let [local (- id base)
                  [offset length expected]
                  (locking index
                    (.seek index (* 44 local))
                    (let [offset (.readLong index) length (.readInt index) hash (byte-array 32)]
                      (.readFully index hash) [offset length hash]))
                  _ (when-not (and (<= 0 offset) (<= 1 length 16777216)
                                   (<= (+ offset length) (.size channel)))
                      (m/fail "Invalid verified ModuleData row bounds" {:native-id local}))
                  bytes (read-at! channel offset length)
                  _ (when-not (Arrays/equals ^bytes expected ^bytes (sha bytes))
                      (m/fail "ModuleData backing content changed" {:native-id local}))
                  edge (fn [x] (if (contains? x :immediate)
                                 (native/native-scalar (data/decimal! (:immediate x) false))
                                 (m/->Ref (+ base (:ref x)))))
                  raw (parse bytes)
                  _ (when-not (= local (:id raw)) (m/fail "Verified ModuleData row ID mismatch" {:native-id local}))
                  node (data/node! raw edge maximum-bytes)]
              (.put ^LinkedHashMap cache id node)
              (when (> (.size ^LinkedHashMap cache) cache-limit)
                (let [iter (.iterator (.keySet ^LinkedHashMap cache))] (.next iter) (.remove iter)))
              node)))))
  java.io.Closeable
  (close [_] (locking cache (reset! closed true) (.clear ^LinkedHashMap cache) (.close channel) (.close index))))

(defn- describe [world source manifest root actual]
  (let [get-node #(when (m/ref? %) (heap/lookup-node source (:id %)))
             root-node (get-node root)
             _ (when-not (= :array (:kind root-node)) (m/fail "ModuleData root must be an array" {}))
             roots (:fields root-node)
             name-value (fn [value]
                          (loop [value value parts [] seen #{}]
                            (if (and (native/native-scalar? value) (zero? (native/payload value)))
                              (reduce (fn [parent [kind x]] [kind parent x]) ["anonymous"] (reverse parts))
                              (let [node (get-node value) [parent item] (:fields node)]
                                (when-not (and (m/ref? value) (not (contains? seen (:id value)))
                                               (= :ctor (:kind node)) (= 2 (count (:fields node)))
                                               (contains? #{1 2} (:tag node)))
                                  (m/fail "Invalid transported Name" {}))
                                (recur parent (conj parts (if (= 1 (:tag node))
                                                           ["str" (:text (get-node item))]
                                                           ["num" (str (native/nat-value {:ref? m/ref? :node (fn [_ ref] (get-node ref))} nil item))]))
                                       (conj seen (:id value)))))))
             part (fn [p]
                    (let [i (data/count! (:rootIndex p) :rootIndex (dec (count roots)))
                          value (nth roots i) node (get-node value)]
                      (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 5 (count (:fields node)))
                                     (= 2 (get-in p [:artifact :oleanVersion]))
                                     (= (get-in manifest [:input :leanCommit]) (get-in p [:artifact :leanCommit])))
                        (m/fail "Invalid transported ModuleData part" {:rootIndex i}))
                      (let [info (:moduleData p)
                            [imports names constants extra entries] (mapv get-node (:fields node))
                            arrays [imports names constants extra entries]
                            is-module (get (:scalar-bytes node) 40)]
                        (when-not (and (every? #(= :array (:kind %)) arrays)
                                       (= (count (:fields imports)) (count (:imports info)))
                                       (= (count (:fields names)) (:constNamesCount info))
                                       (= (count (:fields constants)) (:constantCount info))
                                       (= (count (:fields extra)) (:extraConstNamesCount info))
                                       (= (count (:fields entries)) (count (:extensions info)))
                                       (contains? #{0 1} is-module)
                                       (= (= 1 is-module) (:isModule info)))
                          (m/fail "Transported ModuleData summary mismatch" {:rootIndex i}))
                        (doseq [[import expected] (map vector (:fields imports) (:imports info))]
                          (let [import (get-node import) flags (mapv #(get (:scalar-bytes import) %) [8 9 10])]
                            (when-not (and (= :ctor (:kind import)) (= 0 (:tag import))
                                           (= 1 (count (:fields import))) (every? #{0 1} flags)
                                           (= (name-value (first (:fields import))) (:module expected))
                                           (= flags (mapv #(if (get expected %) 1 0) [:importAll :isExported :isMeta])))
                              (m/fail "Transported import summary mismatch" {:rootIndex i}))))
                        (doseq [[entry expected] (map vector (:fields entries) (:extensions info))]
                          (let [pair (get-node entry) values (get-node (second (:fields pair)))]
                            (when-not (and (= :ctor (:kind pair)) (= 0 (:tag pair))
                                           (= 2 (count (:fields pair))) (= :array (:kind values))
                                           (= (name-value (first (:fields pair))) (:name expected))
                                           (= (count (:fields values)) (:entryCount expected)))
                              (m/fail "Transported extension summary mismatch" {:rootIndex i})))))
                      (assoc p :value value)))
             modules (mapv #(-> % (update :parts (fn [xs] (mapv part xs)))
                                    (update :irParts (fn [xs] (mapv part xs)))) (get-in manifest [:input :modules]))]
         {:world world :root root :roots roots :modules modules :manifest manifest :source source
          :sha256 actual :required-runtime-adapters data/required-runtime-adapters}))

(defn- attach [world source manifest root actual base n]
  (when (some #(<= base % (+ base n -1)) (keys (:heap world)))
    (m/fail "ModuleData guest heap ID collision" {}))
  (let [world (-> world (update :native-imports (fnil conj []) source) (assoc :next-id (+ base n))
                       (update-in [:stats :allocations] + n)
                       (update :heartbeat-allocation-offset (fnil + 0) n))]
    (describe world source manifest root actual)))

(defn describe-attached
  "Recover the receiver description of an already verified, open Store attached
   by identity to WORLD. Does not reopen files, reserve IDs, retain guest roots,
   or repeat the source/index bytehash. Indexed row reads remain hash checked.
   Rejects overlapping sources and any local shadow in the immutable range."
  [world source]
  (when-not (instance? Store source)
    (m/fail "Expected an attached verified ModuleData Store" {}))
  (when @(:closed source) (m/fail "ModuleData source is closed" {}))
  (let [base (:base source) end (+ base (:size source))
        sources (:native-imports world)]
    (when-not (and (= 1 (count (filter #(identical? source %) sources)))
                   (<= end (:next-id world))
                   (not-any? #(and (integer? %) (<= base %) (< % end)) (keys (:heap world)))
                   (every? #(or (identical? source %)
                                (and (instance? Store %)
                                     (integer? (:base %)) (integer? (:size %))
                                     (or (<= (+ (:base %) (:size %)) base)
                                         (<= end (:base %))))) sources))
      (m/fail "Verified ModuleData Store is absent, duplicated, overlapping or shadowed" {}))
    (let [manifest (:manifest source) edge (:root manifest)
          root (if (contains? edge :ref) (m/->Ref (+ base (:ref edge)))
                 (native/native-scalar (data/decimal! (:immediate edge) false)))]
      (describe world source manifest root (:digest source)))))

(defn load-file
  "Validate all nodes, edges, profile and digest; reserve a disjoint guest ID
   range and return the module-data receiver result without hydrating its heap.
   :sha256 pins expected source bytes; actual digest is always calculated.
   :cache-size bounds derived immutable nodes (default1024). Closing :source
   invalidates worlds using it; callers must retain it for their snapshots."
  ([world path] (load-file world path {}))
  ([world path {:keys [sha256 max-nodes max-bytes cache-size max-row-bytes]
                :or {max-nodes 25000000 max-bytes 8589934592 cache-size 1024 max-row-bytes 16777216}}]
   (when (contains? #{:running :paused :suspended :host-call} (:status world))
     (m/fail "ModuleData import requires an idle top-level world" {}))
   (data/count! max-nodes :max-nodes 25000000)
   (data/count! cache-size :cache-size 65536)
   (data/count! max-row-bytes :max-row-bytes 16777216)
   (let [file (io/file path) file-length (.length file)
         _ (data/count! file-length :file-bytes max-bytes)
         base (data/count! (:next-id world) :next-id (- Long/MAX_VALUE max-nodes))
         index-file (java.io.File/createTempFile "lean-native-dag-" ".index")
         digest (MessageDigest/getInstance "SHA-256")
         raw-digest (MessageDigest/getInstance "SHA-256")
         discovered (volatile! 0)
         edge (fn [x]
                (when-not (and (map? x) (= 1 (count x))) (m/fail "Invalid ModuleData edge" {}))
                (if (contains? x :immediate)
                  (native/native-scalar (data/decimal! (:immediate x) false))
                  (let [id (data/count! (:ref x) :ref (dec max-nodes))]
                    (when (> id @discovered) (m/fail "Non-BFS or unreachable ModuleData reference" {}))
                    (when (= id @discovered) (vswap! discovered inc))
                    (m/->Ref (+ base id)))))
         resources (atom [])]
     (try
       (let [[manifest root n actual]
             (with-open [raw-in (DigestInputStream. (io/input-stream file) raw-digest)
                         in (BufferedReader. (InputStreamReader. raw-in
                                               (doto (.newDecoder StandardCharsets/UTF_8)
                                                 (.onMalformedInput CodingErrorAction/REPORT)
                                                 (.onUnmappableCharacter CodingErrorAction/REPORT))) 1048576)
                         out (DataOutputStream. (BufferedOutputStream. (io/output-stream index-file) 1048576))]
               (let [first-line (or (line! in max-row-bytes) (byte-array 0))
                     _ (.update digest first-line) _ (.update digest (byte 10))
                     manifest (data/manifest! (parse first-line)) root (edge (:root manifest))]
                 (loop [offset (inc (alength first-line)) n 0 tags {} layouts {} total 0]
                   (if-let [bytes (line! in max-row-bytes)]
                     (let [raw (parse bytes)]
                       (when-not (and (= n (:id raw)) (< n @discovered) (< n max-nodes))
                         (m/fail "Invalid ModuleData node order/count" {:expected n}))
                       (data/node! raw edge max-bytes)
                       (.writeLong out offset) (.writeInt out (alength bytes)) (.write out (sha bytes))
                       (.update digest bytes) (.update digest (byte 10))
                       (recur (+ offset (alength bytes) 1) (inc n)
                              (update tags (str (:tag raw)) (fnil inc 0))
                              (if (= "ctor" (:kind raw))
                                (update layouts [(:tag raw) (count (:fields raw)) (quot (count (:bytesHex raw)) 2)] (fnil inc 0)) layouts)
                              (+ total (:objectBytes raw))))
                     (do
                       (when-not (and (= n @discovered (get-in manifest [:inventory :nodes]))
                                      (= offset file-length)
                                      (= total (get-in manifest [:inventory :sourceAllocationBytes]))
                                      (= tags (into {} (map (fn [[k v]] [(name k) v])) (get-in manifest [:inventory :tags])))
                                      (= layouts (into {} (map (fn [x] [[(:tag x) (:objectFields x) (:scalarBytesWithPadding x)] (:count x)]))
                                                       (get-in manifest [:inventory :constructorLayouts]))))
                         (m/fail "ModuleData inventory/graph mismatch" {}))
                       (let [canonical (.digest digest) raw (.digest raw-digest)]
                         (when-not (Arrays/equals ^bytes canonical ^bytes raw)
                           (m/fail "ModuleData requires canonical LF-terminated UTF8 rows" {}))
                         [manifest root n (hex raw)]))))))
             _ (when (and sha256 (not= sha256 actual)) (m/fail "ModuleData content digest mismatch" {}))
             _ (when (some #(<= base % (+ base n -1)) (keys (:heap world)))
                 (m/fail "ModuleData guest heap ID collision" {}))
             channel (.getChannel (RandomAccessFile. file "r"))
             _ (swap! resources conj channel)
             index (RandomAccessFile. index-file "r")
             _ (swap! resources conj index)
             _ (io/delete-file index-file)
             source (->Store base n manifest actual channel index (LinkedHashMap. 16 0.75 true) cache-size max-bytes (atom false))
             result (attach world source manifest root actual base n)]
         result)
       (catch Throwable error
         (doseq [resource @resources] (.close ^java.io.Closeable resource))
         (io/delete-file index-file true)
         (throw error))))))

(defn- digest-file [path]
  (with-open [in (io/input-stream path)]
    (let [digest (MessageDigest/getInstance "SHA-256") buffer (byte-array 1048576)]
      (loop [] (let [n (.read in buffer)] (when (pos? n) (.update digest buffer 0 n) (recur))))
      (hex (.digest digest)))))

(defn open-verified
  "Reattach a previously published verified index. The caller MUST pin the
   descriptor SHA256 obtained from a complete validation/publication run.
   Rehashes source and index bytes before exposing data, without JSON-reparsing
   every proof object. :source-path is required and can differ across machines."
  [world descriptor-path expected-descriptor-sha256 {:keys [source-path cache-size]
                                                   :or {cache-size 1024}}]
  (when-not (and (string? expected-descriptor-sha256)
                 (re-matches #"[0-9a-f]{64}" expected-descriptor-sha256)
                 (= expected-descriptor-sha256 (digest-file descriptor-path)))
    (m/fail "Verified ModuleData descriptor digest mismatch" {}))
  (when (contains? #{:running :paused :suspended :host-call} (:status world))
    (m/fail "ModuleData import requires an idle top-level world" {}))
  (let [descriptor (json/read-str (slurp descriptor-path) :key-fn keyword)
        _ (when-not (= "lean-module-verified-index/1" (:schema descriptor))
            (m/fail "Unsupported verified ModuleData index" {}))
        _ (data/count! cache-size :cache-size 65536)
        manifest (data/manifest! (:manifest descriptor))
        n (data/count! (:nodes descriptor) :nodes 25000000)
        base (data/count! (:next-id world) :next-id (- Long/MAX_VALUE n))
        index-name (:indexFile descriptor)
        _ (when-not (and (string? index-name) (= index-name (.getName (io/file index-name))))
            (m/fail "Invalid verified ModuleData index path" {}))
        index-file (io/file (.getParentFile (.getAbsoluteFile (io/file descriptor-path))) index-name)
        _ (when-not (and source-path (= n (get-in manifest [:inventory :nodes]))
                         (= (* 44 n) (.length index-file) (:indexBytes descriptor))
                         (= (.length (io/file source-path)) (:sourceBytes descriptor))
                         (= (:sourceSha256 descriptor) (digest-file source-path)))
            (m/fail "Verified ModuleData source/index digest mismatch" {}))
        ;; Pin index storage to a private inode. Published index mutation after
        ;; its initial bytehash must not change the trusted per-row hashes.
        private-index (java.io.File/createTempFile "lean-native-verified-" ".index")
        _ (try
            (Files/copy (.toPath index-file) (.toPath private-index)
                        (into-array java.nio.file.CopyOption [StandardCopyOption/REPLACE_EXISTING]))
            (when-not (= (:indexSha256 descriptor) (digest-file private-index))
              (m/fail "Verified ModuleData source/index digest mismatch" {}))
            (catch Throwable error (io/delete-file private-index true) (throw error)))
        channel (.getChannel (RandomAccessFile. (io/file source-path) "r"))
        index (RandomAccessFile. private-index "r")
        _ (io/delete-file private-index)

        source (->Store base n manifest (:sourceSha256 descriptor) channel index
                        (LinkedHashMap. 16 0.75 true) cache-size (:sourceBytes descriptor) (atom false))
        root-edge (:root manifest)
        root (if (contains? root-edge :ref) (m/->Ref (+ base (:ref root-edge)))
                 (native/native-scalar (data/decimal! (:immediate root-edge) false)))]
    (try (attach world source manifest root (:sourceSha256 descriptor) base n)
         (catch Throwable error (.close source) (throw error)))))
