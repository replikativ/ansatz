(ns ansatz-lean-jvm-value-checks
  "Structural models only. ModelNode is NOT an interpreter Node; no guest value
   or native authority is constructed. Root separately runs genuine results."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [ansatz.lean.jvm.value :as value] [ansatz.lean.jvm.ir :as ir])
  (:import [java.math BigInteger] [java.util Optional List] [ansatz.lean.jvm LeanUnit]))
(deftype ModelNode [tag rc fields scalars dead array ref readyTask closure metadata])
(defn- model-field [name]
  (doto (.getDeclaredField ModelNode name) (.setAccessible true)))
(def model-ctx {:class ModelNode :node-class ModelNode :tag (model-field "tag") :rc (model-field "rc")
                :fields (model-field "fields") :scalars (model-field "scalars")})
(def ^:dynamic *witnesses* nil)
(defn- leaf [kind] {"kind" kind})
(defn- product [a b] {"kind" "product" "first" a "second" b})
(defn- option [a] {"kind" "option" "element" a})
(defn- list-type [a] {"kind" "list" "element" a})
(defn- node
  ([tag fields] (node tag fields {}))
  ([tag fields flags]
   (ModelNode. tag (get flags :rc 1) (object-array fields) (byte-array (get flags :scalar-bytes 0))
               (get flags :dead false) (get flags :array false) (get flags :ref false)
               (get flags :ready-task false) (:closure flags) (:metadata flags))))
(defn- model-list [elements]
  (reduce (fn [tail head] (node 1 [head tail])) (long 0) (rseq (vec elements))))
(defn- decode [type raw] (value/decode model-ctx type *witnesses* raw))
(defn- io-entry [type]
  {"typeCheck" {"signature" {"arguments" [] "result" type "effect" "io"}}
   "codecWitnesses" *witnesses*})
(defn- code-of [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:code (ex-data error)))))

(deftest leaf-carriers-stay-type-directed
  (is (= BigInteger/ZERO (decode (leaf "nat") (long 0))))
  (is (= (BigInteger/valueOf Long/MIN_VALUE) (decode (leaf "int") Long/MIN_VALUE)))
  (is (= (.shiftLeft BigInteger/ONE 80) (decode (leaf "nat") (.shiftLeft BigInteger/ONE 80))))
  (is (false? (decode (leaf "bool") (long 0))))
  (is (identical? LeanUnit/INSTANCE (decode (leaf "unit") (long 0))))
  (is (= "λ😀\u0000" (decode (leaf "string") "λ😀\u0000")))
  (is (= "RuntimeBoundary" (code-of #(decode (leaf "bool") (long 2))))))
(deftest immutable-products-and-nested-container-results
  (let [raw (node 0 [(long 9) (model-list ["a" "λ\u0000"])])
        result (decode (product (leaf "nat") (list-type (leaf "string"))) raw)]
    (is (instance? List result))
    (is (= [(BigInteger/valueOf 9) ["a" "λ\u0000"]] (vec (map #(if (instance? List %) (vec %) %) result))))
    (is (thrown? UnsupportedOperationException (.set ^List result 0 :mutation)))
    (is (thrown? UnsupportedOperationException (.add ^List (.get ^List result 1) "mutation")))))
(deftest none-some-unit-and-some-none-remain-distinct
  (let [none ^Optional (decode (option (leaf "unit")) (long 0))
        some ^Optional (decode (option (leaf "unit")) (node 1 [(long 0)]))
        nested ^Optional (decode (option (option (leaf "nat"))) (node 1 [(long 0)]))]
    (is (not (.isPresent none)))
    (is (.isPresent some))
    (is (identical? LeanUnit/INSTANCE (.get some)))
    (is (.isPresent nested))
    (is (not (.isPresent ^Optional (.get nested))))))
(deftest proper-list-spines-are-iterative-and-immutable
  (let [result ^List (decode (list-type (leaf "nat")) (model-list (repeat 512 (long 3))))]
    (is (= 512 (.size result)))
    (is (= (BigInteger/valueOf 3) (.get result 511)))
    (is (thrown? UnsupportedOperationException (.clear result)))))
(deftest dag-sharing-is-copied-without-acquiring-guest-owners
  (let [shared (node 1 [(long 4) (long 0)] {:rc 2}) raw (node 0 [shared shared])
        type (product (list-type (leaf "nat")) (list-type (leaf "nat")))]
    (with-redefs [ir/retain! (fn [& _] (throw (ex-info "Must not INC" {})))
                  ir/release! (fn [& _] (throw (ex-info "Must not DEC" {})))]
      (let [result ^List (decode type raw)]
        (is (= (.get result 0) (.get result 1)))
        (is (not (identical? (.get result 0) (.get result 1))))
        (is (= 2 (.-rc shared)))
        (is (= 1 (.-rc raw)))))))
(deftest cycles-and-improper-list-tails-are-refused
  (let [raw (node 1 [(long 1) (long 0)])]
    (aset ^objects (.-fields raw) 1 raw)
    (is (= "RuntimeBoundary" (code-of #(decode (list-type (leaf "nat")) raw)))))
  (is (= "RuntimeBoundary" (code-of #(decode (list-type (leaf "nat")) (node 1 [(long 1) (long 8)]))))))
(deftest actual-node-kind-extent-tag-and-liveness-are-checked
  (doseq [raw [(Object.) (node 1 [(long 1) (long 2)]) (node 0 [(long 1)])
               (node 0 [(long 1) (long 2)] {:scalar-bytes 1})
               (node 0 [(long 1) (long 2)] {:dead true})
               (node 0 [(long 1) (long 2)] {:array true})
               (node 0 [(long 1) (long 2)] {:ref true})
               (node 0 [(long 1) (long 2)] {:ready-task true})
               (node 0 [(long 1) (long 2)] {:closure (Object.)})
               (node 0 [(long 1) (long 2)] {:metadata (Object.)})
               (node 0 [(long 1) (long 2)] {:rc -1})
               (node 0 [nil (long 2)])]]
    (is (= "RuntimeBoundary" (code-of #(decode (product (leaf "nat") (leaf "nat")) raw))))))
(deftest persistent-zero-count-plain-data-is-still-readable
  (is (= [(BigInteger/valueOf 1) true]
         (vec (decode (product (leaf "nat") (leaf "bool")) (node 0 [(long 1) (long 1)] {:rc 0}))))))
(deftest missing-or-conflicting-witnesses-never-fall-back-to-guessed-layout
  (is (= "RuntimeBoundary" (code-of #(value/decode model-ctx (list-type (leaf "nat")) nil (long 0)))))
  (is (= "RuntimeBoundary"
         (code-of #(value/decode model-ctx (option (leaf "nat"))
                                (update *witnesses* "families" conj (first (get *witnesses* "families"))) (long 0))))))
(deftest logical-field-order-uses-the-provided-witness-indices
  ;; Deliberately changed model metadata proves index use only. The shared entry
  ;; validator separately rejects this change against the real native cohort.
  (let [witnesses (update *witnesses* "families"
                          (fn [families]
                            (mapv #(if (= ["str" ["anonymous"] "Prod"] (get % "typeName"))
                                     (update-in % ["constructors" 0 "fields"] (comp vec reverse)) %) families)))]
    (is (= [(BigInteger/valueOf 5) "s"]
           (vec (value/decode model-ctx (product (leaf "nat") (leaf "string")) witnesses
                              (node 0 ["s" (long 5)])))))))
(deftest occurrence-budget-bounds-long-spines-and-dag-expansion
  (is (= "ResourceLimit" (code-of #(decode (list-type (leaf "nat")) (model-list (repeat 50000 (long 1))))))))
(deftest interruption-is-observed-without-clearing-the-callers-flag
  (let [prior (Thread/interrupted)]
    (try
      (.interrupt (Thread/currentThread))
      (let [code (code-of #(decode (leaf "nat") (long 1)))
            interrupted (.isInterrupted (Thread/currentThread))]
        ;; Capture first: test reporting itself is allowed to consume interrupts.
        (Thread/interrupted)
        (is (= "Cancelled" code))
        (is interrupted))
      (finally (Thread/interrupted) (when prior (.interrupt (Thread/currentThread)))))))
(deftest io-success-payload-is-borrowed-and-world-is-not-an-object-field
  (let [type (option (list-type (product (leaf "nat") (leaf "string"))))
        payload (node 1 [(model-list [(node 0 [(long 7) "seven"])])])
        envelope (node 0 [payload]) result (value/decode-io model-ctx (io-entry type) envelope)]
    (is (= :ok (:kind result)))
    (is (.isPresent ^Optional (:value result)))
    (is (= [(BigInteger/valueOf 7) "seven"]
           (vec (.get ^List (.get ^Optional (:value result)) 0))))
    (is (= 1 (.-rc payload)))
    (is (= 1 (.-rc envelope))))
  (is (= "RuntimeBoundary"
         (code-of #(value/decode-io model-ctx (io-entry (leaf "unit")) (node 0 [(long 0) (long 0)]))))))
(deftest io-errors-have-no-exported-guest-alias-and-legacy-has-no-layout-default
  (let [error (node 18 ["model error"]) envelope (node 1 [error])]
    (is (= {:kind :io-error} (value/decode-io model-ctx (io-entry (leaf "nat")) envelope)))
    (is (= 1 (.-rc error)))
    (is (= 1 (.-rc envelope))))
  (is (= "RuntimeBoundary"
         (code-of #(value/decode-io model-ctx {"typeCheck" {"signature" "io-unit"}} (node 0 [(long 0)]))))))

(defn check!
  ([] (check! (io/file "test/fixtures/value-codec-witnesses.json")))
  ([fixture]
   (binding [*witnesses* (json/read-str (slurp fixture))]
     (run-tests 'ansatz-lean-jvm-value-checks))))
