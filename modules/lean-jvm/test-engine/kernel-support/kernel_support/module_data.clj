(ns kernel-support.module-data
  "Receive a pinned, address-free ModuleData DAG into a persistent guest world.
   Scalar words, strings and MPZ retain source identity/representation. Runtime
   typed views must explicitly decode native words and dereference string/MPZ.
   No extension callbacks, initialization, or native Environment finalization run."
  (:refer-clojure :exclude [load-file])
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [kernel-support.carrier :as m]
            [kernel-support.native-scalar :as native]
            [kernel-support.scalar :as scalar])
  (:import [java.io BufferedReader InputStreamReader]
           [java.nio ByteBuffer]
           [java.nio.charset CodingErrorAction StandardCharsets]
           [java.security DigestInputStream MessageDigest]))

(def required-runtime-adapters
  #{:raw-native-scalars :persistent-string-refs :persistent-mpz-refs})

(defn count! [value field maximum]
  (when-not (and (integer? value) (<= 0 value maximum))
    (m/fail "Invalid ModuleData size/index" {:field field :value value :maximum maximum})) value)

(defn bytes! [text]
  (when-not (and (string? text) (even? (count text)) (re-matches #"[0-9a-f]*" text))
    (m/fail "Invalid ModuleData hexadecimal storage" {}))
  (let [^String text text n (.length text)]
    (if (zero? n) []
      (loop [i 0 out (transient [])]
        (if (< i n)
          (let [a (int (.charAt text i)) b (int (.charAt text (inc i)))
                hi (if (<= a 57) (- a 48) (- a 87))
                lo (if (<= b 57) (- b 48) (- b 87))]
            (recur (+ i 2) (conj! out (Integer/valueOf (int (+ (* 16 hi) lo))))))
          (persistent! out))))))

(defn decimal! [text signed?]
  (when-not (and (string? text) (re-matches (if signed? #"0|-?[1-9][0-9]*" #"0|[1-9][0-9]*") text))
    (m/fail "Invalid ModuleData native number" {}))
  (bigint text))

(defn manifest! [manifest]
  (when-not (and (= "manifest" (:kind manifest)) (= "lean-module-dag/1" (:schema manifest))
                 (= 64 (:wordBits manifest)) (= "little" (:byteOrder manifest))
                 (= "unsigned-native-tagged-payload" (:immediateEncoding manifest))
                 (= "4.33.1" (get-in manifest [:input :leanVersion]))
                 (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get-in manifest [:input :leanCommit]))
                 (false? (get-in manifest [:input :nativeEnvironmentFinalized]))
                 (false? (get-in manifest [:input :regionAddressesTransported]))
                 (vector? (get-in manifest [:input :modules])))
    (m/fail "Unsupported ModuleData producer/profile" {}))
  manifest)

(defn- text! [bytes length]
  (when-not (and (seq bytes) (= 0 (peek bytes)))
    (m/fail "ModuleData String lacks NUL terminator" {}))
  (let [raw (byte-array (map unchecked-byte (pop bytes)))
        decoder (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
        text (try (str (.decode decoder (ByteBuffer/wrap raw)))
                  (catch java.nio.charset.CharacterCodingException _
                    (m/fail "Unsupported malformed UTF8 ModuleData String" {})))]
    (when-not (= length (.codePointCount ^String text 0 (.length ^String text)))
      (m/fail "ModuleData String UTF8 length mismatch" {:length length})) text))

(defn node! [raw edge maximum-bytes]
  (let [{:keys [tag kind size capacity objectBytes fields]} raw
        _ (count! tag :tag 255)
        _ (when-not (vector? fields) (m/fail "Invalid ModuleData object fields" {}))
        refs (mapv edge fields)
        bytes (when-not (= "mpz" kind) (bytes! (:bytesHex raw)))
        _ (count! objectBytes :objectBytes maximum-bytes)
        node {:rc 0 :tag tag :fields refs :native-object-bytes objectBytes
              :native-source-id (:id raw)}]
    (case kind
      "ctor"
      (do (when-not (and (<= tag 243) (< (count refs) 256) (true? (:scalarBytesIncludePadding raw))
                         (= objectBytes (+ 8 (* 8 (count refs)) (count bytes))))
            (m/fail "Invalid ModuleData constructor layout" {:id (:id raw)}))
          ;; Existing IR layout guards bound the requested scalar area below
          ;; 1024. Native allocation padding may reach1024; reject that rare
          ;; unsupported case rather than dropping bytes or inventing a split.
          (when (>= (count bytes) 1024) (m/fail "Padded ModuleData scalar tail exceeds guest layout profile" {:id (:id raw)}))
          (cond-> (assoc node :kind :ctor)
            (seq bytes) (assoc :layout {:objects (count refs) :usize 0 :ssize (count bytes)}
                               :scalar-bytes (into {} (map-indexed (fn [i b] [(+ (* 8 (count refs)) i) b])) bytes))))
      "array"
      (do (count! capacity :capacity (quot maximum-bytes 8)) (count! size :size capacity)
          (when-not (and (= tag 246) (= size (count refs)) (empty? bytes) (= objectBytes (+ 24 (* 8 capacity))))
            (m/fail "Invalid ModuleData array layout" {:id (:id raw)}))
          (assoc node :kind :array :native-capacity capacity))
      "scalar-array"
      (let [width (count! (:elementBytes raw) :elementBytes 255)]
        (when (zero? width) (m/fail "Zero ModuleData scalar-array width" {}))
        (count! capacity :capacity (quot maximum-bytes width)) (count! size :size capacity)
        (when-not (and (= tag 248) (empty? refs) (= (count bytes) (* size width)) (= objectBytes (+ 24 (* capacity width))))
          (m/fail "Invalid ModuleData scalar-array layout" {:id (:id raw)}))
        (case width
          1 (assoc node :kind :byte-array :bytes bytes :native-capacity capacity)
          8 (assoc node :kind :float-array :native-capacity capacity
                   :values (mapv #(scalar/float-from-bytes "float" (vec %)) (partition 8 bytes)))
          (assoc node :kind :scalar-array :element-bytes width :bytes bytes :native-capacity capacity)))
      "string"
      (do (count! capacity :capacity maximum-bytes) (count! size :size capacity)
          (count! (:utf8Length raw) :utf8Length size)
          (when-not (and (= tag 249) (empty? refs) (= size (count bytes)) (= objectBytes (+ 32 capacity)))
            (m/fail "Invalid ModuleData String layout" {:id (:id raw)}))
          (assoc node :kind :string :text (text! bytes (:utf8Length raw)) :utf8-bytes (pop bytes)
                 :native-byte-size size :native-utf8-length (:utf8Length raw) :native-capacity capacity))
      "mpz"
      (do (when-not (and (= tag 250) (empty? refs) (nil? (:bytesHex raw)))
            (m/fail "Invalid ModuleData MPZ layout" {:id (:id raw)}))
          (assoc node :kind :mpz :integer (decimal! (:signedDecimal raw) true)))
      (m/fail "Unsupported ModuleData object kind" {:kind kind :tag tag}))))

(defn load-file
  "Read and validate flattened JSONL into an immutable world. Forward references
  become persistent Ref IDs; nothing is exposed until every node is validated.
  Options :sha256 expected digest, :max-nodes(default10m), :max-bytes(default2GiB).
  Returns :world, :root, :roots, :modules (parts carry :value), :manifest, :sha256,
  and :required-runtime-adapters. This does not execute the imported extension
  callbacks or assert that all required runtime adapters have been installed."
  ([world path] (load-file world path {}))
  ([world path {:keys [sha256 max-nodes max-bytes]
                :or {max-nodes 10000000 max-bytes 2147483648}}]
   (when (contains? #{:running :paused :suspended :host-call} (:status world))
     (m/fail "ModuleData import requires an idle top-level world" {:status (:status world)}))
   (count! max-nodes :max-nodes 10000000) (count! max-bytes :max-bytes Long/MAX_VALUE)
   (when (> (.length (io/file path)) max-bytes) (m/fail "ModuleData file byte limit exceeded" {}))
   (let [digest (MessageDigest/getInstance "SHA-256")
         base (count! (:next-id world) :next-id (- Long/MAX_VALUE max-nodes))
         discovered (volatile! 0)
         edge (fn [edge]
                (when-not (and (map? edge) (= 1 (count edge))) (m/fail "Invalid ModuleData edge" {}))
                (if (contains? edge :immediate)
                  (native/native-scalar (decimal! (:immediate edge) false))
                  (let [id (count! (:ref edge) :ref (dec max-nodes))]
                    (when (> id @discovered) (m/fail "Non-BFS or unreachable ModuleData reference" {:id id :discovered @discovered}))
                    (when (= id @discovered) (vswap! discovered inc))
                    (m/->Ref (+ base id)))))]
     (with-open [input (DigestInputStream. (io/input-stream path) digest)
                 reader (BufferedReader. (InputStreamReader. input StandardCharsets/UTF_8))]
       (let [manifest (manifest! (json/read-str (or (.readLine reader) "null") :key-fn keyword))
             root (edge (:root manifest))
             [heap n tags]
             (loop [heap (transient (:heap world)) n 0 tags {}]
               (if-let [line (.readLine reader)]
                 (let [raw (json/read-str line :key-fn keyword)]
                   (when-not (and (= n (:id raw)) (< n @discovered) (< n max-nodes))
                     (m/fail "Invalid ModuleData node order/count" {:id (:id raw) :expected n}))
                   (when (contains? (:heap world) (+ base n))
                     (m/fail "ModuleData guest heap ID collision" {:id (+ base n)}))
                   (let [node (node! raw edge max-bytes)]
                     (recur (assoc! heap (+ base n) node) (inc n) (update tags (str (:tag raw)) (fnil inc 0)))))
                 [(persistent! heap) n tags]))
             actual-sha256 (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest)))]
         (when-not (= n @discovered (get-in manifest [:inventory :nodes]))
           (m/fail "ModuleData missing referenced nodes" {:nodes n :discovered @discovered}))
         (when-not (= tags (into {} (map (fn [[k v]] [(name k) v])) (get-in manifest [:inventory :tags])))
           (m/fail "ModuleData tag inventory mismatch" {}))
         (when (and sha256 (not= sha256 actual-sha256))
           (m/fail "ModuleData content digest mismatch" {:expected sha256 :actual actual-sha256}))
         (let [world (-> world (assoc :heap heap :next-id (+ base n)) (update-in [:stats :allocations] + n))
               root-node (when (m/ref? root) (m/node world root))
               _ (when-not (= :array (:kind root-node)) (m/fail "ModuleData root must be an array" {}))
               roots (:fields root-node)
               part (fn [part]
                      (let [index (count! (:rootIndex part) :rootIndex (dec (count roots)))
                            value (nth roots index) node (when (m/ref? value) (m/node world value))]
                        (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 5 (count (:fields node)))
                                       (= 2 (get-in part [:artifact :oleanVersion]))
                                       (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get-in part [:artifact :leanCommit])))
                          (m/fail "Invalid transported ModuleData part" {:rootIndex index}))
                        (assoc part :value value)))
               modules (mapv #(-> % (update :parts (fn [xs] (mapv part xs)))
                                    (update :irParts (fn [xs] (mapv part xs)))) (get-in manifest [:input :modules]))]
           {:world world :root root :roots roots :modules modules :manifest manifest
            :sha256 actual-sha256 :required-runtime-adapters required-runtime-adapters}))))))
