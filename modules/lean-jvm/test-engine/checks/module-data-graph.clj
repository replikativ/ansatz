(ns java-ir-module-data-graph
  "Bounded native ModuleData DAG conversion. Does not allocate a legacy World,
   run import/finalization, authorize executable IR, or issue base authority."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [kernel-support.module-data :as transport]
            [java-ir-baseline :as j])
  (:import [java.io BufferedReader InputStreamReader]
           [java.nio.charset StandardCharsets]
           [java.security DigestInputStream MessageDigest]))

(def limits {:source-bytes (* 32 1024 1024) :source-nodes 150000
             :normalized-nodes 150000 :edges 1000000})
(defn- check! [ok message data]
  (when-not ok (throw (ex-info message data))))
(defn- digest-text [digest]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest ^MessageDigest digest))))
(defn- scan
  "Validate every source record; retain only immutable leaves and small census.
   Visitor borrows each raw/validated node. No source graph is retained."
  [path visitor]
  (check! (<= (.length (io/file path)) (:source-bytes limits)) "ModuleData source byte bound" {})
  (let [digest (MessageDigest/getInstance "SHA-256") discovered (volatile! 0)
        edge (fn [e]
               (check! (and (map? e) (= 1 (count e))) "Invalid ModuleData edge" {})
               (if (contains? e :immediate)
                 (let [n (transport/decimal! (:immediate e) false)]
                   (check! (<= n Long/MAX_VALUE) "Native immediate exceeds 63-bit payload" {})
                   (long n))
                 (let [id (transport/count! (:ref e) :ref (dec (:source-nodes limits)))]
                   (check! (<= id @discovered) "Non-BFS ModuleData reference" {:id id})
                   (when (= id @discovered) (vswap! discovered inc))
                   ;; Validation identity only; the converter uses GraphRef later.
                   {:source-id id})))]
    (with-open [stream (DigestInputStream. (io/input-stream path) digest)
                reader (BufferedReader. (InputStreamReader. stream StandardCharsets/UTF_8))]
      (let [manifest (transport/manifest! (json/read-str (or (.readLine reader) "null") :key-fn keyword))
            _ (check! (= {:ref 0} (:root manifest)) "ModuleData aggregate root must be source zero" {})
            _ (edge (:root manifest))
            result
            (loop [n 0 counts {} tags {} leaves {} normalized 0 edges 0 ambiguous [] mpz [] part-ids nil]
              (if-let [line (.readLine reader)]
                (let [raw (json/read-str line :key-fn keyword)
                      _ (check! (and (= n (:id raw)) (< n @discovered) (< n (:source-nodes limits)))
                                "ModuleData record order/count" {:id (:id raw) :expected n})
                      node (transport/node! raw edge (:source-bytes limits))
                      kind (:kind raw)
                      _ (check! (contains? #{"ctor" "array" "string" "mpz"} kind)
                                "Unsupported ModuleData Java kind" {:kind kind})
                      leaf? (contains? #{"string" "mpz"} kind)
                      normalized (+ normalized (if leaf? 0 1))
                      edges (+ edges (count (:fields raw)))
                      _ (check! (and (<= normalized (:normalized-nodes limits)) (<= edges (:edges limits)))
                                "ModuleData aggregate graph bound" {})
                      part-ids (if (zero? n)
                                 (do (check! (= "array" kind) "ModuleData aggregate root must be Array" {})
                                     (check! (every? #(and (= #{:ref} (set (keys %)))
                                                           (integer? (:ref %))) (:fields raw))
                                             "ModuleData aggregate parts must be references" {})
                                     (mapv :ref (:fields raw))) part-ids)
                      _ (when (some #{n} part-ids)
                          (check! (and (= "ctor" kind) (= 0 (:tag raw)) (= 5 (count (:fields raw))))
                                  "Invalid authentic ModuleData part layout" {:id n}))
                      ambiguous (reduce-kv
                                  (fn [out i e]
                                    (if (and (:immediate e) (> (bigint (:immediate e)) Integer/MAX_VALUE))
                                      (conj out [n i (:immediate e)]) out)) ambiguous (:fields raw))
                      mpz (if (= "mpz" kind) (conj mpz [n (:integer node)]) mpz)
                      leaves (if leaf? (assoc leaves n (if (= "string" kind) (:text node) (biginteger (:integer node)))) leaves)]
                  (visitor raw node)
                  (recur (inc n) (update counts kind (fnil inc 0)) (update tags (str (:tag raw)) (fnil inc 0))
                         leaves normalized edges ambiguous mpz part-ids))
                {:source-nodes n :kinds counts :tags tags :leaves leaves :normalized-nodes normalized
                 :edges edges :ambiguous-immediates ambiguous :mpz mpz :part-ids part-ids}))
            actual (digest-text digest)]
        (check! (= (:source-nodes result) @discovered (get-in manifest [:inventory :nodes]))
                "ModuleData missing referenced records" {})
        (check! (= (:tags result) (into {} (map (fn [[k v]] [(name k) v])) (get-in manifest [:inventory :tags])))
                "ModuleData tag inventory mismatch" {})
        (let [parts (mapcat #(concat (:parts %) (:irParts %)) (get-in manifest [:input :modules]))
              indexes (mapv :rootIndex parts)]
          (check! (and (= (count indexes) (count (:part-ids result)))
                       (= (set indexes) (set (range (count (:part-ids result))))))
                  "ModuleData requires complete genuine part roots" {})
          (doseq [part parts]
            (check! (and (= 2 (get-in part [:artifact :oleanVersion]))
                         (= (get-in manifest [:input :leanCommit]) (get-in part [:artifact :leanCommit])))
                    "ModuleData part provenance differs" {})))
        (assoc result :sha256 actual :manifest manifest)))))

(defn audit
  "Streaming census, including every ambiguous immediate slot and MPZ leaf.
   This report is descriptive and confers no typed-domain authority."
  [path]
  (dissoc (scan path (fn [_ _])) :leaves))

(defn prepare
  "Convert one complete authenticated aggregate. SHA256 is required from the
   caller's accepted artifact evidence, not learned from this operation.
   DOMAIN is the trusted adapter's source-bound typed-use proof callback. It is
   called with [sha256 node-id field-index decimal] for every immediate above
   INT_MAX, and must return :nat or :unsigned (never inferred from physical tag).
   All MPZ must be nonnegative and outside native small-Nat range; smaller/negative
   MPZ need a distinct reviewed domain profile. Leaves are memoized by source ID.
   No guest callback or runtime execution occurs. Return the graph and census together;
   the caller owns source/runtime leases and must authenticate finalization later."
  [basis source state-token path {:keys [sha256 domain]}]
  (check! (and (string? sha256) (re-matches #"[0-9a-f]{64}" sha256)) "Expected artifact SHA256 required" {})
  (let [first-pass (scan path (fn [_ _]))
        _ (check! (= sha256 (:sha256 first-pass)) "ModuleData artifact digest mismatch" {})
        _ (doseq [[id field decimal] (:ambiguous-immediates first-pass)]
            (check! (and (fn? domain) (contains? #{:nat :unsigned} (domain [sha256 id field decimal])))
                    "Unaudited native immediate domain" {:id id :field field :decimal decimal}))
        _ (doseq [[id value] (:mpz first-pass)]
            (check! (> value Long/MAX_VALUE) "Unsupported ambiguous/small/negative MPZ domain" {:id id}))
        leaves (:leaves first-pass)
        edge (fn [e] (if-let [text (:immediate e)] (long (transport/decimal! text false))
                        (let [id (:ref e)] (if (contains? leaves id) (get leaves id) (j/graph-ref basis id)))))
        nodes (java.util.ArrayList.)
        second-pass (scan path
                      (fn [raw _]
                        (when (contains? #{"ctor" "array"} (:kind raw))
                          (.add nodes (j/graph-node basis
                                        (cond-> {:id (:id raw) :kind (keyword (:kind raw))
                                                 :fields (mapv edge (:fields raw))}
                                          (= "ctor" (:kind raw))
                                          (assoc :tag (:tag raw) :scalars (mapv unchecked-byte (transport/bytes! (:bytesHex raw))))))))))
        _ (check! (= sha256 (:sha256 second-pass)) "ModuleData source changed during conversion" {})
        census (dissoc first-pass :leaves)]
    {:graph (j/module-data-graph basis source state-token nodes (j/graph-ref basis 0))
     :census census :profile :module-data-rc0-v1}))
