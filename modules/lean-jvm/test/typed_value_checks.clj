(ns typed-value-checks
  "Actual detached-storage view checks. The Java fixture is private test evidence,
  and deliberately confers no source/native entry admission."
  (:require [clojure.test :refer [deftest is testing run-tests]]
            [ansatz.lean.jvm.typed-value :as value])
  (:import [ansatz.lean.jvm LeanType LeanData LeanUnit LeanChoice LeanBytes]
           [java.util Optional List]
           [java.lang.reflect Modifier]))

(defn- field [object name]
  (.get (doto (.getDeclaredField (class object) name) (.setAccessible true)) object))
(defn- fixture-types []
  (let [fixture (Class/forName "ansatz.lean.jvm.PublicDatatypeChecks")
        method (doto (.getDeclaredMethod fixture "fixture" (make-array Class 0)) (.setAccessible true))]
    (into {} (field (.invoke method nil (object-array 0)) "types"))))
(defn- packet [types]
  (let [^LeanType type (.get types 0)
        constructor (first (.constructors type))]
    (.create constructor [42 4294967295 (byte-array [1 2 -1]) (Optional/of LeanUnit/INSTANCE)
                          [1 2 3] (.create (first (.constructors ^LeanType (.get types 7))) [99]) true (float -0.0) (int \λ) -128])))

(deftest rejected-input-adapters-are-not-evaluated
  (let [types (fixture-types) raw (packet types)
        fields (.fields (.constructor raw))
        array-type (.type ^ansatz.lean.jvm.LeanType$Field (nth fields 4))
        option-type (.type ^ansatz.lean.jvm.LeanType$Field (nth fields 3))
        touched (atom 0)
        lazy-input (map (fn [x] (swap! touched inc) x) [1 2 3])
        custom-list (proxy [java.util.AbstractList] []
                      (size [] (swap! touched inc) 1)
                      (get [_] (swap! touched inc) 1))
        custom-map (proxy [clojure.lang.APersistentMap] []
                     (count [] (swap! touched inc) 1)
                     (seq [] (swap! touched inc) (seq {:some nil})))
        custom-key (proxy [Object] [] (hashCode [] (swap! touched inc) 1))
        bad-tags (array-map custom-key nil)
        comparator-tags (sorted-map-by (fn [a b] (swap! touched inc) (compare a b)) :some nil)
        forged-view (value/->TypedVector nil custom-list nil nil)
        forged-fields (assoc (value/materialize (value/view (.type raw) raw)) :lean/fields forged-view)]
    (reset! touched 0)
    (doseq [input [lazy-input (list 1 2 3) custom-list (java.util.Collections/unmodifiableList custom-list)]]
      (is (thrown? IllegalArgumentException (value/host-value array-type input))))
    (is (thrown? IllegalArgumentException (value/host-value option-type custom-map)))
    (is (thrown? IllegalArgumentException (value/host-value option-type bad-tags)))
    (is (thrown? IllegalArgumentException (value/host-value option-type comparator-tags)))
    (is (thrown? IllegalArgumentException (value/host-value (.type raw) forged-fields)))
    (is (thrown? IllegalArgumentException (value/materialize forged-view)))
    (is (zero? @touched))
    (is (= [1 2 3] (value/host-value array-type [1 2 3])))
    (is (= [1 2 3] (value/host-value array-type (java.util.LinkedList. [1 2 3]))))))

(deftest nominal-map-is-a-complete-immutable-collection
  (let [types (fixture-types) raw (packet types) type (.type raw)
        x (value/view type raw) ordinary (value/materialize x)
        ;; Bytes keep immutable value identity until explicit byte copying.
        comparable (assoc-in ordinary [:lean/fields 2] (nth (:lean/fields x) 2))]
    (is (Modifier/isFinal (.getModifiers (class x))))
    (is (not (instance? clojure.lang.IProxy x)))
    (is (= #{:lean/type :lean/constructor :lean/fields} (set (keys x))))
    (is (= 3 (count x)))
    (is (= 3 (reduce-kv (fn [n _ _] (inc n)) 0 x)))
    (is (= :stopped (reduce-kv (fn [_ _ _] (reduced :stopped)) nil x)))
    (is (= x comparable))
    (is (= comparable x))
    (is (= (hash x) (hash comparable)))
    (is (= (.hashCode x) (.hashCode comparable)))
    (is (identical? raw (value/unwrap x)))
    (is (identical? raw (value/host-value type x)))
    (is (= (:lean/type x) (x :lean/type)))
    (is (= :missing (x :missing :missing)))
    (is (thrown? clojure.lang.ArityException (x)))
    (is (thrown? clojure.lang.ArityException (x 1 2 3)))
    (is (thrown? clojure.lang.ArityException (apply x (range 25))))
    (is (thrown? clojure.lang.ArityException (.call ^java.util.concurrent.Callable x)))
    (is (= :extra (:extra (assoc x :extra :extra))))
    (is (= 2 (count (dissoc x :lean/type))))
    (is (= 3 (count x)))
    (is (= {:test true} (meta (assoc (with-meta x {:test true}) :x 1))))
    (is (thrown? UnsupportedOperationException (.put ^java.util.Map x :x 1)))
    (is (thrown? UnsupportedOperationException (.clear ^java.util.Map x)))
    (is (instance? (Class/forName "[B") (get-in ordinary [:lean/fields 2])))
    (is (= {:some nil} (get-in x [:lean/fields 3])))
    (is (= \λ (get-in x [:lean/fields 8])))
    (is (= raw (.create type (value/host-value type x))))
    (is (= raw (.create type (value/host-value type ordinary))))))

(deftest indexed-fields-have-ordinary-vector-semantics
  (let [types (fixture-types) x (value/view (.get types 0) (packet types))
        fields (:lean/fields x) elements (nth fields 4)]
    (is (vector? fields))
    (is (vector? elements))
    (is (= [1 2 3] elements))
    (is (= elements [1 2 3]))
    (is (= (hash [1 2 3]) (hash elements)))
    (is (= 2 (elements 1)))
    (is (= :missing (nth elements 99 :missing)))
    (is (= [1 9 3] (assoc elements 1 9)))
    (is (= [1 2 3 4] (conj elements 4)))
    (is (= [1 2] (pop elements)))
    (is (= [3 2 1] (rseq elements)))
    (is (.equals (java.util.ArrayList. (vec (seq elements))) elements))
    (is (.equals elements (java.util.ArrayList. (vec (seq elements)))))
    (is (= [1 2 3] (vec (.toArray ^List elements))))
    (is (thrown? UnsupportedOperationException (.add ^List elements 4)))
    (is (thrown? UnsupportedOperationException (.set ^List elements 0 4)))
    (is (= {:test true} (meta (assoc (with-meta elements {:test true}) 0 8))))))

(deftest unit-option-and-conversion-are-type-directed
  (let [types (fixture-types) ^LeanType unit (.get types 5) ^LeanType option (.get types 4)]
    (is (nil? (value/view unit LeanUnit/INSTANCE)))
    (is (nil? (value/view option (Optional/empty))))
    (is (= {:some nil} (value/view option (Optional/of LeanUnit/INSTANCE))))
    (is (identical? LeanUnit/INSTANCE (value/host-value unit nil)))
    (is (.isPresent ^Optional (value/host-value option {:some nil})))
    (is (identical? LeanUnit/INSTANCE (.get ^Optional (value/host-value option {:some nil}))))
    (is (not (.isPresent ^Optional (value/host-value option nil))))
    (is (thrown? IllegalArgumentException (value/host-value option {:some nil :extra true})))
    (testing "host conversion observes cancellation without clearing the interrupt"
      (let [thread (Thread/currentThread)
            [failure preserved?]
            (try
              (.interrupt thread)
              (let [failure (try (value/host-value option {:some nil}) nil
                                 (catch java.util.concurrent.CancellationException failure failure))]
                [failure (.isInterrupted thread)])
              (finally (Thread/interrupted)))]
        ;; Capture before clojure.test reporting, whose counter updates may use
        ;; interruptible synchronization on the current thread.
        (is (instance? java.util.concurrent.CancellationException failure))
        (is preserved?)))))

(deftest iterative-collection-algorithms-match-clojure
  (doseq [x [nil [] {} [1 2N 3.0] {:a [1 nil {:some nil}] :b false}]]
    (is (= (hash x) (value/collection-hash x)))
    (is (= (.hashCode (or x [])) (value/collection-hash (or x []) false))))
  (let [a (reduce (fn [x _] [x]) 1 (range 4000))
        b (reduce (fn [x _] [x]) 1N (range 4000))]
    (is (value/collection-equal a b))
    (is (= (value/collection-hash a) (value/collection-hash b)))))

(defn- descriptive-branch-type [kind]
  ;; Reflection builds only a descriptive test type, never storage or entry
  ;; evidence. Real construction remains covered by the Java storage tests.
  (let [^LeanType unit (get (fixture-types) 5)
        registry (field unit "registry")
        constructor (doto (first (.getDeclaredConstructors LeanType)) (.setAccessible true))
        logical (case kind
                  "sum" {"kind" kind "left" {"kind" "unit"} "right" {"kind" "nat"}}
                  "except" {"kind" kind "error" {"kind" "unit"} "value" {"kind" "nat"}})]
    (.newInstance constructor (object-array [registry (int 100) {"type" logical} (apply str (repeat 64 "b"))]))))

(deftest sum-and-except-retain-explicit-unit-branch-tags
  (doseq [[kind left right] [["sum" :left :right] ["except" :error :ok]]]
    (let [type (descriptive-branch-type kind)
          raw (LeanChoice/left LeanUnit/INSTANCE)
          x (value/view type raw)]
      (is (= {left nil} x))
      (is (= x {left nil}))
      (is (= {left nil} (value/materialize x)))
      (is (identical? raw (value/host-value type x)))
      (is (.isLeft ^LeanChoice (value/host-value type {left nil})))
      (is (identical? LeanUnit/INSTANCE (.value ^LeanChoice (value/host-value type {left nil}))))
      (is (= {right 42} (value/view type (LeanChoice/right 42))))
      (is (not (.isLeft ^LeanChoice (value/host-value type {right 42}))))
      (is (thrown? IllegalArgumentException (value/host-value type {left nil right 42}))))))

(defn- recursive-types []
  (let [fixture (Class/forName "TypedStorageChecks")
        read (fn [name] (.invoke (doto (.getDeclaredMethod fixture name (make-array Class 0)) (.setAccessible true)) nil (object-array 0)))
        bridge (Class/forName "ansatz.lean.jvm.ValueBridge")
        compile (doto (.getDeclaredMethod bridge "compileTrusted" (into-array Class [Class java.util.Map java.util.Map])) (.setAccessible true))
        registry (.invoke compile nil (object-array [(Class/forName "ansatz.lean.jvm.internal.exec.Interpreter")
                                                    (read "native004Logical") (read "native004Normalized")]))]
    (into {} (field registry "types"))))

(deftest lean-list-sequencing-uses-the-linear-java-iterator
  (let [types (recursive-types) ^LeanType ast (get types 0) ^LeanType list-type (get types 3)
        leaf (.create (first (.constructors ast)) [7])
        source (.create list-type (vec (repeat 512 leaf)))
        x (value/view list-type source)]
    (is (= 512 (count x)))
    (is (= 3584 (reduce + (map #(get-in % [:lean/fields 0]) x))))
    (is (identical? source (value/unwrap x)))
    (is (identical? source (value/host-value list-type x)))
    (is (identical? source (value/host-value list-type source)))
    (is (= (hash (vec (seq x))) (hash x)))
    (is (= x (vec (seq x))))
    (is (= (vec (seq x)) x))))

(deftest detached-deep-recursive-views-use-iterative-value-operations
  (let [types (recursive-types) ^LeanType ast (get types 0) ^LeanType list-type (get types 3)
        leaf (.create (first (.constructors ast)) [7])
        branch (nth (.constructors ast) 2)
        raw (reduce (fn [child _] (.create branch [(.create list-type [child])])) leaf (range 180))
        a (value/view ast raw) b (value/view ast raw)
        ordinary (value/materialize a)]
    (is (= a b))
    (is (= a ordinary))
    (is (= ordinary a))
    (is (= (hash a) (hash b)))
    (is (= (hash a) (hash ordinary)))
    (is (= raw (.create ast (value/host-value ast ordinary))))))
