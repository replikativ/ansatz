(ns prototype.module-store-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.module-data :as data]
            [prototype.module-store :as store]
            [prototype.native-heap :as heap])
  (:import [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]))

(defn- previous-parse [bytes]
  (let [decoder (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))]
    (json/read-str (str (.decode decoder (ByteBuffer/wrap bytes))) :key-fn keyword)))
(defn- parse-outcome [parse bytes]
  (try (let [value (parse bytes)] [:ok (some-> value class) value])
       (catch Throwable error [:error (class error) (.getMessage error) (ex-data error)])))

(deftest ascii-row-decoding-preserves-json-and-strict-utf8-results
  (let [texts ["" "{}" "[]" "null" "false" "true" "0" "-0" "-123.5" "1e12" "-1.25e-9"
               "9223372036854775808" "{\"nested\":[1,true,null,{\"value\":\"\\u03bb\"}]}"
               "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" "\"\\ud83d\\ude00\""
               "{\"éλ😀\":\"العربية 日本語\"}" "\"𝄞\"" "\"λ\"" "\"é\""
               "{" "[1,]" "{\"a\":}" "\"unterminated" "\u0000" "\"a\u0001b\""
               (json/write-str (apply str (map char (range 128))))]
        malformed [[-1] [-64 -128] [-63 -65] [-62] [-30 -126] [-16 -97 -104]
                   [-128] [-65] [-32 -128 -128] [-16 -128 -128 -128]
                   [-19 -96 -128] [-19 -65 -65] [-12 -112 -128 -128] [-11 -128 -128 -128]
                   [-2] [-1] [-61 40] [-30 40 -95]]
        inputs (concat (map #(.getBytes ^String % StandardCharsets/UTF_8) texts)
                       (for [n (range 256)] (byte-array [(unchecked-byte n)]))
                       (for [n (range 256)] (byte-array [34 (unchecked-byte n) 34]))
                       (map #(byte-array (map unchecked-byte %)) malformed)
                       (map #(byte-array (map unchecked-byte (concat [34] % [34]))) malformed)
                       [(byte-array (map unchecked-byte [239 187 191 123 125]))])]
    (doseq [[i bytes] (map-indexed vector inputs)]
      (is (= (parse-outcome previous-parse bytes) (parse-outcome #'store/parse bytes))
          (str "UTF8/JSON corpus input " i)))))

(deftest row-decoding-preserves-wrong-carrier-errors
  (doseq [value [nil "{}" [123 125] (object-array [123 125]) (long-array [123 125])
                 (ByteBuffer/wrap (byte-array [123 125])) (Object.)]]
    (is (= (parse-outcome previous-parse value) (parse-outcome #'store/parse value)))))

(deftest lazy-and-eager-native-canary-match-without-hydrating-world
  (let [world (m/world {}) eager (data/load-file world "fixtures/module-data-canary.jsonl")
        lazy (store/load-file world "fixtures/module-data-canary.jsonl" {:sha256 (:sha256 eager) :cache-size 1})
        source (:source lazy)]
    (try
      (is (= (:heap world) (get-in lazy [:world :heap])))
      (is (= (:next-id (:world eager)) (:next-id (:world lazy))))
      (is (= (:roots eager) (:roots lazy)))
      (is (not (heap/imported? [source] -1)))
      (is (nil? (heap/lookup [source] (:next-id (:world lazy)))))
      (let [before (hash (:world lazy))]
        (doseq [id (range 8)] (heap/lookup-node source id))
        (is (= before (hash (:world lazy)))))
      (doseq [[id node] (:heap (:world eager))]
        (is (heap/imported? [source] id))
        (is (= node (heap/lookup [source] id)))
        (is (<= (.size ^java.util.LinkedHashMap (:cache source)) 1)))
      (is (= (:sha256 eager) (:sha256 lazy)))
      (let [world (:world lazy) mutable (u/thaw world)]
        (is (identical? (:native-imports world) (:native-imports (u/freeze mutable))))
        (doseq [[id node] (:heap (:world eager))]
          (is (= node (m/node world (m/->Ref id))))
          (is (= node (#'u/node mutable (m/->Ref id)))))
        (is (= world (select-keys (u/freeze mutable) (keys world)))))
      (finally (.close source)))))

(deftest describe-existing-store-preserves-world-and-resource-identity
  (let [loaded (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl")
        source (:source loaded) world (:world loaded)]
    (try
      (let [described (store/describe-attached world source)]
        (is (= loaded described))
        (is (identical? world (:world described)))
        (is (identical? source (:source described)))
        (is (false? @(:closed source))))
      (doseq [invalid [(assoc world :native-imports [])
                       (assoc world :native-imports [source source])
                       (assoc world :native-imports [source {:base 999999 :size 1}])
                       (assoc world :next-id (dec (:next-id world)))
                       (assoc-in world [:heap (:base source)] {:kind :ctor})
                       (assoc-in world [:heap (dec (:next-id world))] {:kind :ctor})]]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"absent, duplicated, overlapping or shadowed"
              (store/describe-attached invalid source))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"verified ModuleData Store"
            (store/describe-attached world (into {} (map #(vector % (get source %)) [:base :size])))))
      (.close source)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed"
            (store/describe-attached world source)))
      (finally (.close source)))))

(deftest describe-store-allows-disjoint-verified-sources-and-rejects-overlap
  (let [a (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl")
        b (store/load-file (:world a) "fixtures/module-data-canary.jsonl")
        overlapping (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl")]
    (try
      (is (identical? (:world b) (:world (store/describe-attached (:world b) (:source a)))))
      (is (identical? (:world b) (:world (store/describe-attached (:world b) (:source b)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"overlapping"
            (store/describe-attached (update (:world a) :native-imports conj (:source overlapping)) (:source a))))
      (finally (.close (:source a)) (.close (:source b)) (.close (:source overlapping))))))

(deftest backing-file-mutation-is-detected-before-exposing-uncached-node
  (let [file (java.io.File/createTempFile "module-store-mutation" ".jsonl")]
    (try
      (io/copy (io/file "fixtures/module-data-canary.jsonl") file)
      (let [result (store/load-file (m/world {}) file {:cache-size 0}) source (:source result)]
        (try
          (with-open [raf (java.io.RandomAccessFile. file "rw")]
            (.seek raf (dec (.length raf))) (.write raf (int \x)))
          ;; Corrupting the newline alone is outside the indexed row. Corrupt
          ;; the last JSON byte instead; the source's line digest must reject it.
          (with-open [raf (java.io.RandomAccessFile. file "rw")]
            (.seek raf (- (.length raf) 2)) (.write raf (int \x)))
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"backing content changed"
                (heap/lookup-node source (dec (:next-id (:world result))))))
          (finally (.close source))))
      (finally (io/delete-file file true)))))

(deftest malformed-late-node-is-rejected-even-when-never-requested
  (let [file (java.io.File/createTempFile "module-store-invalid" ".jsonl")]
    (try
      (spit file (clojure.string/replace (slurp "fixtures/module-data-canary.jsonl") "\"tag\":248" "\"tag\":245"))
      (is (thrown? clojure.lang.ExceptionInfo (store/load-file (m/world {}) file)))
      (is (thrown? clojure.lang.ExceptionInfo
            (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl" {:sha256 "wrong"})))
      (finally (io/delete-file file true)))))

(deftest two-imports-reserve-disjoint-ranges-and-old-forks-keep-identity
  (let [a (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl")
        b (store/load-file (:world a) "fixtures/module-data-canary.jsonl")]
    (try
      (is (= 8 (:base (:source b))))
      (is (= 16 (get-in b [:world :next-id])))
      (is (= 2 (count (get-in b [:world :native-imports]))))
      (is (= (m/node (:world a) (first (:roots a)))
             (m/node (:world b) (first (:roots a)))))
      (is (not (heap/imported? (get-in a [:world :native-imports]) 8)))
      (finally (.close (:source a)) (.close (:source b))))))

(def verified-fixture "fixtures/module-data-canary.verified.json")
(def verified-sha "13a03fd9dd2346a535f7c064e1c0f4c5ed514a5a58b1625c8fbdefeb11e24a67")

(deftest pinned-verified-artifact-reopens-without-reparsing-proofs
  (let [a (store/load-file (m/world {}) "fixtures/module-data-canary.jsonl")
        b (store/open-verified (m/world {}) verified-fixture verified-sha
                               {:source-path "fixtures/module-data-canary.jsonl"})]
    (try
      (is (= (:sha256 a) (:sha256 b)))
      (is (= (:roots a) (:roots b)))
      (is (= (:modules a) (:modules b)))
      (doseq [id (range 8)]
        (is (= (heap/lookup-node (:source a) id) (heap/lookup-node (:source b) id))))
      (.close (:source b))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"closed"
            (heap/lookup-node (:source b) 7)))
      (finally (.close (:source a)) (.close (:source b)))))
  (doseq [sha [nil "bad" (apply str (repeat 64 "0"))]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"descriptor digest"
          (store/open-verified (m/world {}) verified-fixture sha
                               {:source-path "fixtures/module-data-canary.jsonl"})))))

(deftest altered-binary-index-is-rejected-even-with-a-pinned-original-descriptor
  (let [directory (.toFile (java.nio.file.Files/createTempDirectory "module-store-index-test" (make-array java.nio.file.attribute.FileAttribute 0)))
        descriptor (io/file directory "module-data-canary.verified.json")
        index (io/file directory "module-data-canary.verified.json.index")]
    (try
      (io/copy (io/file verified-fixture) descriptor)
      (io/copy (io/file (str verified-fixture ".index")) index)
      (with-open [raf (java.io.RandomAccessFile. index "rw")] (.write raf 255))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"source/index digest"
            (store/open-verified (m/world {}) descriptor verified-sha
                                 {:source-path "fixtures/module-data-canary.jsonl"})))
      (finally (io/delete-file descriptor true) (io/delete-file index true) (io/delete-file directory true)))))

(deftest published-index-mutation-after-open-cannot-change-snapshot-index
  (let [directory (.toFile (java.nio.file.Files/createTempDirectory "module-store-live-index" (make-array java.nio.file.attribute.FileAttribute 0)))
        descriptor (io/file directory "module-data-canary.verified.json")
        index (io/file directory "module-data-canary.verified.json.index")]
    (try
      (io/copy (io/file verified-fixture) descriptor)
      (io/copy (io/file (str verified-fixture ".index")) index)
      (let [opened (store/open-verified (m/world {}) descriptor verified-sha
                                       {:source-path "fixtures/module-data-canary.jsonl" :cache-size 0})]
        (try
          (with-open [raf (java.io.RandomAccessFile. index "rw")]
            (.seek raf (* 44 7)) (.write raf 255))
          (is (= :string (:kind (heap/lookup-node (:source opened) 7))))
          (finally (.close (:source opened)))))
      (finally (io/delete-file descriptor true) (io/delete-file index true) (io/delete-file directory true)))))
