(ns java-ir-byte-array-empty-checks
  "Original borrowed-capacity ByteArray allocation, live size, COW and fork."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as host] [java-ir-byte-array-checks :as bytes]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-byte-array-empty-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn raw [] (get (first (filter #(= "ByteArray.emptyWithCapacity" (get % "label")) (records))) "row"))
(defn context [explicit]
  (let [rows (mapv #(get % "row") (concat (records) (bytes/originals)))
        helpers [(c/decl "empty-pap" [] "object"
                   (c/let-ir 1 "object" {:pap {:c (get-in (first (filter #(= "ByteArray.emptyWithCapacity._boxed" (get % "label")) (records))) ["row" "name"]) :ys []}} (c/ret 1)))
                 (c/decl "empty-ap" [(c/p 1 "object") (c/p 2 "tobject")] "object"
                   (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))]]
    (assoc *basis* :explicit explicit :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw helpers))]))))
(defn capacity [ctx value] (alength ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value)))
(defn empty! [ctx e n] (j/call ctx e "ByteArray.emptyWithCapacity._boxed" [n]))
(defn counters [e] (mapv #(host/private-value e %) ["allocations" "stores" "retains" "releases"]))

(deftest pinned-fixture-and-exact-borrowed-native-abi
  (let [manifest (edn/read-string (slurp (str directory "provenance.edn"))) r (raw)
        method (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map]))]
    (is (= 3 (count (records))))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (:extern-inventory-sha256 manifest) (corpus/sha256 (str directory "extern-inventory.json"))))
    (is (= "lean_mk_empty_byte_array" (j/invoke-static method [r])))
    (is (= [{"borrow" true "ty" "tobject" "x" {"idx" 1}}] (get-in r ["ir" "extern" "xs"])))
    (doseq [bad [(assoc-in r ["ir" "extern" "xs" 0 "borrow"] false)
                 (assoc-in r ["ir" "extern" "xs" 0 "ty"] "usize")
                 (assoc-in r ["ir" "extern" "type"] "tagged")]]
      (is (g/bad? #(j/invoke-static method [bad]))))))

(deftest exact-capacity-zero-live-size-and-owned-result-in-both-drivers
  (doseq [explicit [false true] n [0 1 8 (biginteger 8)]]
    (let [ctx (context explicit) e (j/machine ctx) before (counters e) a (empty! ctx e n)]
      (try
        (is (= [1 0 0 0] (mapv - (counters e) before)))
        (is (= (long n) (capacity ctx a)))
        (is (= [] (bytes/payload ctx a))) (is (= 1 (c/rc ctx a)))
        (is (= 248 (.getInt ^java.lang.reflect.Field (:tag ctx) a)))
        (is (zero? (alength ^objects (.get ^java.lang.reflect.Field (:fields ctx) a))))
        (j/retain! ctx e a)
        (is (= 0 (j/call ctx e "ByteArray.size._boxed" [a])))
        (is (= 1 (c/rc ctx a)))
        (finally (j/release! ctx e a) (j/close! ctx e))))))

(deftest original-empty-closed-body-and-owned-pap-ap-wrapper
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx)
          a (j/call ctx e "ByteArray.empty._closed_0" [])
          closure (j/call ctx e "empty-pap" [])
          b (j/call ctx e "empty-ap" [closure 7])]
      (try
        (is (= [] (bytes/payload ctx a) (bytes/payload ctx b)))
        (is (= 0 (capacity ctx a))) (is (= 7 (capacity ctx b)))
        (is (= 1 (c/rc ctx b)))
        (finally (j/release! ctx e a) (j/release! ctx e b) (j/close! ctx e))))))

(deftest spare-capacity-is-not-live-and-unique-push-reuses-storage
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (empty! ctx e 4)]
      (try
        (doseq [v [0 127 128 255]]
          (let [before (counters e)]
            (is (identical? a (bytes/push! ctx e a v)))
            (is (= [0 1 0 0] (mapv - (counters e) before)))))
        (is (= [0 127 128 255] (bytes/payload ctx a)))
        (is (= 4 (capacity ctx a)))
        (is (= 255 (bytes/read! ctx e a 3)))
        (finally (j/release! ctx e a) (j/close! ctx e))))))

(deftest shared-empty-push-copies-and-fork-preserves-independent-size-and-capacity
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) a (empty! ctx e 8)]
      (j/retain! ctx e a)
      (let [b (bytes/push! ctx e a 7)]
        (is (not (identical? a b)))
        (is (= [] (bytes/payload ctx a))) (is (= [7] (bytes/payload ctx b)))
        (is (= 8 (capacity ctx a) (capacity ctx b)))
        (is (= 1 (c/rc ctx a) (c/rc ctx b)))
        (j/release! ctx e b))
      (let [child (j/fork! ctx e [a a]) ce (:engine child) [b alias] (:roots child)]
        (try
          (is (identical? b alias)) (is (not (identical? a b)))
          (is (= [] (bytes/payload ctx b))) (is (= 8 (capacity ctx b)))
          (is (identical? b (bytes/push! ctx ce b 255)))
          (is (= [] (bytes/payload ctx a))) (is (= [255] (bytes/payload ctx b)))
          (is (= 8 (capacity ctx a) (capacity ctx b)))
          (is (identical? a (bytes/push! ctx e a 128)))
          (is (= [128] (bytes/payload ctx a))) (is (= [255] (bytes/payload ctx b)))
          (is (not (identical? (.get ^java.lang.reflect.Field (:scalars ctx) a)
                               (.get ^java.lang.reflect.Field (:scalars ctx) b))))
          (finally (j/release! ctx e a) (j/release! ctx ce b) (j/close! ctx e) (j/close! ctx ce)))))))

(deftest over-profile-or-invalid-capacity-rejects-before-allocation-or-ownership-effects
  (doseq [explicit [false true] n [-1 0.5 "0" (biginteger "18446744073709551616") 16777217]]
    (let [ctx (context explicit) e (j/machine ctx) before (counters e)]
      (try
        (is (g/bad? #(empty! ctx e n)))
        (is (= before (counters e)))
        (finally
          ;; Failed explicit guest operations retain their continuation; this
          ;; test does not invent an unsupported failure unwind.
          (if (= "failed" (j/phase ctx e))
            (is (g/bad? #(j/close! ctx e)))
            (j/close! ctx e)))))))

(deftest raw-borrowed-entry-and-closure-refuse-without-native-effects
  (doseq [explicit [false true]]
    (let [ctx (context explicit) e (j/machine ctx) before (counters e)]
      (try
        (is (re-find #"Borrowed ByteArray primitive" (c/failure #(j/call ctx e "ByteArray.emptyWithCapacity" [8]))))
        (is (g/bad? #(j/make-closure! ctx e "ByteArray.emptyWithCapacity" [])))
        (is (= before (counters e))) (is (= "idle" (j/phase ctx e)))
        (finally (j/close! ctx e))))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-byte-array-empty-checks)))
