(ns ansatz.research.ir.node-decoder-checks-v1
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-array-checks :as arr]
            [java-ir-pointer-checks :as ptr]
            [ansatz.research.ir.node-decoder-v1 :as decoder]))
(def ^:dynamic *basis* nil)
(def directory "fixtures/")
(defn hex-bytes [s]
  (byte-array (map #(unchecked-byte (Integer/parseInt % 16)) (re-seq #".." s))))
(defn native-fixture []
  (let [file (io/file directory "ir-value-native.jsonl")
        digest (java.security.MessageDigest/getInstance "SHA-256")
        bytes (java.nio.file.Files/readAllBytes (.toPath file))]
    (is (= "af68df3d04a38a71ebdb45863ffaac6ff954b89d1f9458b2b21b5d09b480e2bd"
           (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest bytes)))))
    (with-open [r (io/reader file)] (mapv json/read-str (line-seq r)))))
(defn install-native! [basis rows]
  ;; Fixture-only import: collapse authentic String/MPZ storage to the Java
  ;; runtime's scalar representations. No compiler-output authority follows.
  (let [ctx (j/prepare-host-program basis [] [])
        source (j/source-binding ctx (Object.))
        records (into {} (map (juxt #(get % "id") identity) (rest rows)))
        value (fn value [v]
                (if (contains? v "immediate")
                  (j/graph-int ctx (bigint (get v "immediate")))
                  (let [id (get v "ref") row (get records id)]
                    (case (get row "kind")
                      "string" (let [bs (hex-bytes (get row "bytesHex"))]
                                 ;; Producer utf8Length counts characters; size
                                 ;; is the byte extent including the final NUL.
                                 (String. bs 0 (dec (int (get row "size"))) java.nio.charset.StandardCharsets/UTF_8))
                      "mpz" (j/graph-int ctx (bigint (get row "signedDecimal")))
                      (j/graph-ref ctx (inc id))))))
        nodes (mapv (fn [r]
                      (j/graph-node ctx
                        (cond-> {:kind (keyword (get r "kind")) :id (inc (get r "id"))
                                 :fields (mapv value (get r "fields"))}
                          (= "ctor" (get r "kind"))
                          (assoc :tag (get r "tag") :scalars (hex-bytes (get r "bytesHex"))))))
                    (filter #(contains? #{"ctor" "array"} (get % "kind")) (rest rows)))
        engine (j/machine ctx)
        graph (j/selected-owner-graph ctx source (Object.) nodes [] [] [(value (get (first rows) "root"))])]
    {:ctx ctx :engine engine :root (first (j/install-graph! ctx engine graph))}))
(defn open! [ctx engine & [limits]]
  (decoder/open-decoder ctx engine
    (merge {:deadline-nanos (+ (System/nanoTime) 30000000000)} limits)))
(deftest authentic-54-declarations-match-native-json-and-close-revokes-memo
  (let [{:keys [ctx engine root]} (install-native! *basis* (native-fixture))
        d (open! ctx engine)]
    (try
      (let [expected (json/read-str (slurp (io/file directory "ir-value-native.expected.json")) :key-fn keyword)
            actual ((:project d) [:array :decl] root)]
        (is (= 54 (count actual)))
        (is (true? (= expected actual)))
        (is (= actual ((:project d) [:array :decl] root)))
        (is (pos? (:memo-nodes ((:stats d)))))
        ((:close! d))
        (is (thrown? clojure.lang.ExceptionInfo ((:project d) [:array :decl] root)))
        (is (zero? (:memo-nodes ((:stats d))))))
      (finally ((:close! d)) (j/close! ctx engine)))))
(deftest engine-close-invalidates-a-previously-memoized-root
  (let [{:keys [ctx engine root]} (install-native! *basis* (native-fixture))
        d (open! ctx engine)]
    (try
      ((:project d) [:array :decl] root)
      (j/close! ctx engine)
      (is (thrown? clojure.lang.ExceptionInfo ((:project d) [:array :decl] root)))
      (finally ((:close! d)) (j/close! ctx engine)))))
(deftest independent-node-and-output-limits-reject-the-native-fixture
  (doseq [limits [{:max-nodes 1} {:max-output 2} {:max-array 4} {:max-chars 100}]]
    (let [{:keys [ctx engine root]} (install-native! *basis* (native-fixture))
          d (open! ctx engine limits)]
      (try
        (is (thrown? clojure.lang.ExceptionInfo ((:project d) [:array :decl] root)))
        (is (false? (:open? ((:stats d)))))
        (finally ((:close! d)) (j/close! ctx engine))))))
(deftest scalar-nat-bit-limits-agree-for-long-and-big-integer
  (doseq [wrap [long biginteger]]
    (let [ctx (j/prepare-host-program *basis* [] []) engine (j/machine ctx)
          d (open! ctx engine {:max-nat-bits 1})]
      (try
        (is (= 0 ((:project d) :nat (wrap 0))))
        (is (= 1 ((:project d) :nat (wrap 1))))
        (is (thrown? clojure.lang.ExceptionInfo ((:project d) :nat (wrap 2))))
        (finally ((:close! d)) (j/close! ctx engine))))))
(deftest array-view-uses-live-size-and-progress-invalidates-cached-view
  (let [ctx (binding [arr/*basis* *basis*] (arr/context)) engine (j/machine ctx)
        a (arr/push! ctx engine (arr/empty! ctx engine 8) 7)
        d (open! ctx engine)]
    (try
      (is (= 8 (alength ^objects (arr/fields ctx a))))
      (is (= ["object"] ((:project d) [:array :ir-type] a)))
      (is (= ["object"] ((:project d) [:array :ir-type] a)))
      (is (= 1 (:memo-nodes ((:stats d)))))
      (j/retain! ctx engine a)
      (is (thrown? clojure.lang.ExceptionInfo ((:project d) [:array :ir-type] a)))
      (finally ((:close! d)) (j/release! ctx engine a) (j/release! ctx engine a) (j/close! ctx engine)))))
(deftest dead-node-guard-runs-before-typed-memo-hit
  ;; Deliberately unsafe storage model: alter only dead, without engine progress,
  ;; to isolate the guard from the separate paused-invocation stamp.
  (let [ctx (binding [arr/*basis* *basis*] (arr/context)) engine (j/machine ctx)
        a (arr/empty! ctx engine 4) d (open! ctx engine)
        dead (doto (.getDeclaredField (class a) "dead") (.setAccessible true))]
    (try
      (is (= [] ((:project d) [:array :decl] a)))
      (.setBoolean dead a true)
      (is (thrown? clojure.lang.ExceptionInfo ((:project d) [:array :decl] a)))
      (finally (.setBoolean dead a false) ((:close! d)) (j/release! ctx engine a) (j/close! ctx engine)))))
(deftest invalid-and-deep-schema-selection-fails-before-memo-hashing
  (doseq [kind [:unknown [:array :unknown] [[:array :nat] :nat]
                (nth (iterate #(vector :array %) :nat) 2000)]]
    (let [ctx (j/prepare-host-program *basis* [] []) engine (j/machine ctx) d (open! ctx engine)]
      (try
        (is (thrown? clojure.lang.ExceptionInfo ((:project d) kind 0)))
        (is (false? (:open? ((:stats d)))))
        (finally ((:close! d)) (j/close! ctx engine))))))
(deftest pointer-stamped-foreign-branch-is-rejected-and-projection-does-not-acquire
  (let [name-row (c/decl "decoder-name" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "tobject" (c/lit 0)
                     (c/let-ir 3 "object" (c/ctor 1 [(c/v 2) (c/v 1)] 8) (c/ret 3))))
        ctx (assoc (binding [ptr/*basis* *basis*] (ptr/prepare [name-row])) :explicit true)
        engine (j/machine ctx) a (j/call ctx engine "decoder-name" ["forked"])]
    (try
      (is (= 1 (ptr/same ctx engine a a)))
      (let [{child :engine [b] :roots} (j/fork! ctx engine [a])
            d (open! ctx engine)
            before [(j/instructions ctx engine) (c/rc ctx a) (ptr/word a)]]
        (try
          (is (= ["str" ["anonymous"] "forked"] ((:project d) :name a)))
          (is (= ["str" ["anonymous"] "forked"] ((:project d) :name a)))
          (is (= before [(j/instructions ctx engine) (c/rc ctx a) (ptr/word a)]))
          (is (thrown? clojure.lang.ExceptionInfo ((:project d) :name b)))
          (finally ((:close! d)) (j/release! ctx child b) (j/close! ctx child))))
      (finally (j/release! ctx engine a) (j/close! ctx engine)))))
(deftest malformed-structural-cycle-is-rejected-without-recursive-walking
  ;; Unsafe cycle model, with its immediate child restored before guest release.
  (let [row (c/decl "body-model" [] "object"
              (c/let-ir 1 "tobject" (c/lit 0)
                (c/let-ir 2 "tobject" (c/lit 1)
                  (c/let-ir 3 "tobject" (c/lit 12)
                    (c/let-ir 4 "object" (c/ctor 6 [(c/v 1) (c/v 2) (c/v 3)] 2)
                      (c/ret 4))))))
        ctx (binding [c/*basis* *basis*] (c/prepare [row])) engine (j/machine ctx)
        root (j/call ctx engine "body-model" []) fields ^objects (.get ^java.lang.reflect.Field (:fields ctx) root)]
    (aset fields 2 root)
    (let [d (open! ctx engine)]
      (try
        (is (thrown? clojure.lang.ExceptionInfo ((:project d) :body root)))
        (is (false? (:open? ((:stats d)))))
        (finally (aset fields 2 (long 12)) ((:close! d)) (j/release! ctx engine root) (j/close! ctx engine))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'ansatz.research.ir.node-decoder-checks-v1)))
