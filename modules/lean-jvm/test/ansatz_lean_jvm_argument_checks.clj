(ns ansatz-lean-jvm-argument-checks
  "Host-only recipe models; fixtures confer no native or allocation authority."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [ansatz.lean.jvm.argument :as argument])
  (:import [java.math BigInteger] [java.util ArrayList List Optional Map AbstractList]
           [ansatz.lean.jvm LeanUnit]))
(def ^:dynamic *witnesses* nil)
(defn- leaf [kind] {"kind" kind})
(defn- product [a b] {"kind" "product" "first" a "second" b})
(defn- option [a] {"kind" "option" "element" a})
(defn- list-type [a] {"kind" "list" "element" a})
(defn- descriptor [types] {"arguments" types "result" (leaf "unit") "effect" "pure"})
(defn- jlist [& elements] (ArrayList. ^java.util.Collection (vec elements)))
(defn- plan [types & inputs] (argument/plan (descriptor types) *witnesses* (object-array inputs)))
(defn- code-of [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:code (ex-data error)))))
(defn- linear-plan? [{:keys [constructors roots]}]
  (let [owners (int-array (count constructors))]
    (and (every? true?
                 (map-indexed
                  (fn [index {:keys [fields]}]
                    (every? (fn [field]
                              (if (map? field)
                                (let [target (:ref field)]
                                  (and (= #{:ref} (set (keys field))) (integer? target) (<= 0 target) (< target index)
                                       (do (aset owners target (inc (aget owners target))) true)))
                                (#{Long BigInteger String} (class field)))) fields)) constructors))
         (every? (fn [root]
                   (if (map? root)
                     (let [target (:ref root)]
                       (and (integer? target) (<= 0 target) (< target (count constructors))
                            (do (aset owners target (inc (aget owners target))) true)))
                     (#{Long BigInteger String} (class root)))) roots)
         (every? #(= 1 %) owners))))

(deftest primitive-planning-uses-the-existing-exact-codec
  (let [large (.shiftLeft BigInteger/ONE 80)
        result (plan [(leaf "nat") (leaf "int") (leaf "bool") (leaf "string") (leaf "unit")]
                     large -7 true "λ😀\u0000" LeanUnit/INSTANCE)]
    (is (= {:constructors [] :roots [large -7 1 "λ😀\u0000" 0]} result))
    (is (linear-plan? result)))
  (is (= "InvalidArgument" (code-of #(plan [(leaf "nat")] -1))))
  (is (= "UnsupportedArgumentType" (code-of #(plan [(leaf "bool")] 1))))
  (is (= "UnsupportedArgumentType" (code-of #(plan [(leaf "unit")] nil)))))

(deftest empty-and-nested-optional-unit-remain-distinct
  (is (= {:constructors [] :roots [0]} (plan [(option (leaf "unit"))] (Optional/empty))))
  (is (= {:constructors [{:tag 1 :fields [0]}] :roots [{:ref 0}]}
         (plan [(option (leaf "unit"))] (Optional/of LeanUnit/INSTANCE))))
  (is (= {:constructors [{:tag 1 :fields [0]}] :roots [{:ref 0}]}
         (plan [(option (option (leaf "nat")))] (Optional/of (Optional/empty))))))

(deftest products-and-empty-lists-have-witnessed-linear-recipes
  (let [result (plan [(product (list-type (leaf "nat")) (leaf "string"))] (jlist (jlist) "empty"))]
    (is (= {:constructors [{:tag 0 :fields [0 "empty"]}] :roots [{:ref 0}]} result))
    (is (linear-plan? result))
    (is (thrown? UnsupportedOperationException (.put ^Map result :roots [])))
    (is (thrown? UnsupportedOperationException (.set ^List (:constructors result) 0 :changed)))))

(deftest list-head-subtrees-precede-parents-and-tails-are-iterative
  (let [input (ArrayList. ^java.util.Collection (vec (repeat 512 (Optional/of LeanUnit/INSTANCE))))
        result (plan [(list-type (option (leaf "unit")))] input)]
    (is (= 1024 (count (:constructors result))))
    (is (linear-plan? result))))

(deftest mutable-host-arrays-and-lists-are-not-retained
  (let [input (jlist 1 2) arguments (object-array [input])
        result (argument/plan (descriptor [(list-type (leaf "nat"))]) *witnesses* arguments)]
    (.set input 0 99) (aset arguments 0 nil)
    (is (= {:constructors [{:tag 1 :fields [2 0]} {:tag 1 :fields [1 {:ref 0}]}] :roots [{:ref 1}]} result))))

(deftest shared-host-subtrees-are-copied-and-cycles-refused
  (let [shared (jlist 7) result (plan [(product (list-type (leaf "nat")) (list-type (leaf "nat")))]
                                    (jlist shared shared))]
    (is (= 3 (count (:constructors result))))
    (is (= [{:ref 0} {:ref 1}] (get-in result [:constructors 2 :fields])))
    (is (linear-plan? result)))
  (let [cyclic (ArrayList.)]
    (.add cyclic cyclic)
    (is (= "InvalidArgument" (code-of #(plan [(list-type (list-type (leaf "nat")))] cyclic))))))

(deftest finite-carrier-and-arity-requirements-precede-traversal
  (is (= "UnsupportedArgumentType" (code-of #(argument/plan (descriptor []) nil []))))
  (is (= "ArityMismatch" (code-of #(argument/plan (descriptor [(leaf "nat")]) nil (object-array 0)))))
  (doseq [input [nil (object-array [1 2]) (jlist 1) (jlist 1 2 3) (Object.)]]
    (is (#{"UnsupportedArgumentType" "InvalidArgument"} (code-of #(plan [(product (leaf "nat") (leaf "nat"))] input)))))
  (is (= "UnsupportedArgumentType" (code-of #(plan [(option (leaf "nat"))] (jlist)))))
  (let [realized (atom 0) lazy-input (lazy-seq (swap! realized inc) (seq [1]))]
    (is (= "UnsupportedArgumentType" (code-of #(plan [(list-type (leaf "nat"))] lazy-input))))
    (is (zero? @realized)))
  (let [reads (atom 0) input (proxy [AbstractList] []
                              (size [] 100001)
                              (get [_] (swap! reads inc) (throw (AssertionError. "Must not read"))))]
    (is (= "ResourceLimit" (code-of #(plan [(list-type (leaf "nat"))] input))))
    (is (zero? @reads))))

(deftest unsupported-types-and-missing-layouts-fail-even-for-empty-values
  (is (= "RuntimeBoundary"
         (code-of #(argument/plan (descriptor [(list-type (leaf "nat"))]) nil (object-array [(jlist)])))))
  (is (#{"UnsupportedSignature" "UnsupportedArgumentType"}
        (code-of #(plan [(list-type {"kind" "callback"})] (jlist))))))

(deftest field-position-use-is-explicit-not-inferred-from-constructor-shape
  ;; Changed MODEL metadata only. Actual entry admission rejects this cohort change.
  (let [witnesses (update *witnesses* "families"
                          (fn [families]
                            (mapv #(if (= ["str" ["anonymous"] "Prod"] (get % "typeName"))
                                     (update-in % ["constructors" 0 "fields"] (comp vec reverse)) %) families)))
        result (argument/plan (descriptor [(product (leaf "nat") (leaf "string"))]) witnesses (object-array [(jlist 5 "s")]))]
    (is (= {:constructors [{:tag 0 :fields ["s" 5]}] :roots [{:ref 0}]} result))))

(deftest aggregate-and-occurrence-limits-are-checked-before-materialization
  (let [nodes (ArrayList. ^java.util.Collection (vec (repeat 50000 1)))
        strings (ArrayList. ^java.util.Collection (vec (repeat 17 (apply str (repeat 65536 "x")))))
        integers (ArrayList. ^java.util.Collection (vec (repeat 1025 (.shiftLeft BigInteger/ONE 4095))))]
    (is (= "ResourceLimit" (code-of #(plan [(list-type (leaf "nat"))] nodes))))
    (is (= "ResourceLimit" (code-of #(plan [(list-type (leaf "string"))] strings))))
    (is (= "ResourceLimit" (code-of #(plan [(list-type (leaf "nat"))] integers)))))
  (let [type (nth (iterate option (leaf "nat")) 129)]
    ;; The authenticated descriptor bound (32) is stricter than the host walk's 128.
    (is (= "UnsupportedSignature" (code-of #(plan [type] (Optional/empty)))))))

(deftest interruption-is-refused-with-the-callers-flag-preserved
  (let [prior (Thread/interrupted)]
    (try (.interrupt (Thread/currentThread))
         (let [code (code-of #(plan [(leaf "nat")] 1)) flag (.isInterrupted (Thread/currentThread))]
           (Thread/interrupted) (is (= "Cancelled" code)) (is flag))
         (finally (Thread/interrupted) (when prior (.interrupt (Thread/currentThread)))))))

(defn check!
  ([] (check! (io/file "test/fixtures/value-codec-witnesses.json")))
  ([fixture]
   (binding [*witnesses* (json/read-str (slurp fixture))]
     (run-tests 'ansatz-lean-jvm-argument-checks))))
