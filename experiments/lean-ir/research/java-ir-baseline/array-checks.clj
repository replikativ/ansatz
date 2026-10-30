(ns java-ir-array-checks
  "Original array operations: unique storage, selected owners and fork isolation."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-generation-checks :as g] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def fixture "test/fixtures/java-array-runtime/original-rows.json")
(defn originals [] (json/read-str (slurp fixture)))
(defn context []
  (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(mapv #(get % "row") (originals))])))
(defn size [a]
  (.invoke (.getMethod (class a) "arraySize" (make-array Class 0)) a (object-array 0)))
(defn fields [ctx a] (.get ^java.lang.reflect.Field (:fields ctx) a))
(defn elements [ctx a] (vec (take (size a) (fields ctx a))))
(defn empty! [ctx engine capacity] (j/call ctx engine "Array.mkEmpty._boxed" [0 capacity]))
(defn push! [ctx engine a value] (j/call ctx engine "Array.push._boxed" [0 a value]))
(defn pop! [ctx engine a] (j/call ctx engine "Array.pop._boxed" [0 a]))

(deftest original-fixture-and-exact-abis
  (let [manifest (edn/read-string (slurp "test/fixtures/java-array-runtime/provenance.edn"))
        rows (originals)]
    (is (= 28 (count rows)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture)))
    (is (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (:lean-commit manifest)))
    (doseq [r rows :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [(get r "row")]))))))

(deftest capacity-growth-is-geometric-and-unique-push-reuses-storage
  (let [ctx (context) engine (j/machine ctx) a (empty! ctx engine 4)]
    (try
      (is (= 0 (size a))) (is (= 4 (alength ^objects (fields ctx a))))
      (let [b (push! ctx engine a 10) c (push! ctx engine b 20)]
        (is (and (identical? a b) (identical? b c))) (is (= [10 20] (elements ctx c)))
        (is (every? nil? (drop 2 (fields ctx c))))
        (is (= 1 (c/rc ctx c))))
      (finally (j/release! ctx engine a) (j/close! ctx engine)))))

(deftest growth-transfers-element-credits-and-pop-clears-spare-storage
  (let [ctx (context) engine (j/machine ctx)
        source (j/source-binding ctx (Object.))
        [v] (j/install-graph! ctx engine
              (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [42]})]
                [] [] [(j/graph-ref ctx 1)]))
        a (push! ctx engine (empty! ctx engine 1) v)
        b (push! ctx engine a 10)]
    (try
      (is (not (identical? a b)))
      (is (host/private-value a "dead"))
      (is (= 4 (alength ^objects (fields ctx b))))
      (is (= 1 (c/rc ctx v)))
      (is (= [v 10] (elements ctx b)))
      (is (identical? b (pop! ctx engine b)))
      (is (= [v] (elements ctx b)))
      (is (nil? (aget ^objects (fields ctx b) 1)))
      (pop! ctx engine b)
      (is (= 0 (c/rc ctx v))) (is (= 0 (size b)))
      (is (identical? b (pop! ctx engine b)))
      (finally (j/release! ctx engine b) (j/close! ctx engine)))))

(deftest shared-and-persistent-arrays-copy-every-live-alias
  (doseq [source-rc [0 99]]
    (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
          r #(j/graph-ref ctx %)
          [a] (j/install-graph! ctx engine
                (j/selected-owner-graph ctx source (Object.)
                  [(j/graph-node ctx {:kind :array :id 1 :rc source-rc :fields [(r 2) (r 2)]})
                   (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [0]})] [] [] [(r 1)]))
          v (first (elements ctx a))
          _ (j/retain! ctx engine a)
          b (push! ctx engine a 42)]
      (try
        (is (not (identical? a b)))
        (is (= [v v] (elements ctx a)))
        (is (= [v v 42] (elements ctx b)))
        (is (= 4 (c/rc ctx v)))
        (j/release! ctx engine b)
        (is (= 2 (c/rc ctx v)))
        (finally (j/release! ctx engine a) (j/close! ctx engine))))))

(deftest replicate-overwrite-swap-and-list-order-preserve-ownership
  (let [ctx (context) engine (j/machine ctx)
        source (j/source-binding ctx (Object.))
        [v] (j/install-graph! ctx engine
              (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :ctor :id 1 :rc 1 :tag 0 :fields [42]})] [] [] [(j/graph-ref ctx 1)]))
        a (j/call ctx engine "Array.replicate._boxed" [0 3 v])]
    (try
      (is (= 3 (c/rc ctx v)))
      (is (identical? a (j/call ctx engine "Array.set._boxed" [0 a 1 7 0])))
      (is (= 2 (c/rc ctx v)))
      (is (identical? a (j/call ctx engine "Array.swap._boxed" [0 a 0 1 0 0])))
      (is (= [7 v v] (elements ctx a)))
      (let [list (j/call ctx engine "Array.toList._boxed" [0 a])
            first-fields (fields ctx list) tail (aget ^objects first-fields 1)
            second-fields (fields ctx tail) last (aget ^objects second-fields 1)]
        (is (= 7 (aget ^objects first-fields 0)))
        (is (and (identical? v (aget ^objects second-fields 0))
                 (identical? v (aget ^objects (fields ctx last) 0))))
        (is (= 2 (c/rc ctx v)))
        (j/release! ctx engine list)
        (is (= 0 (c/rc ctx v))))
      (finally (j/close! ctx engine)))))

(deftest owned-versus-borrowed-getters-and-forked-capacity
  (let [ctx (context) engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [v] (j/install-graph! ctx engine
              (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :ctor :id 1 :rc 1 :tag 0 :fields [42]})] [] [] [(j/graph-ref ctx 1)]))
        a (push! ctx engine (empty! ctx engine 8) v)]
    (try
      (j/retain! ctx engine a)
      (let [owned (j/call ctx engine "Array.getInternal._boxed" [0 a 0 0])]
        (is (identical? v owned)) (is (= 2 (c/rc ctx v))) (j/release! ctx engine owned))
      (j/retain! ctx engine a)
      (is (identical? v (j/call ctx engine "Array.getInternalBorrowed._boxed" [0 a 0 0])))
      (is (= 1 (c/rc ctx v)))
      (let [child (j/fork! ctx engine [a]) child-engine (:engine child) b (first (:roots child))]
        (try
          (is (= 8 (alength ^objects (fields ctx b))))
          (is (= 1 (size b)))
          (is (identical? b (push! ctx child-engine b 99)))
          (is (= 1 (size a))) (is (= 2 (size b)))
          (is (not (identical? v (first (elements ctx b)))))
          (finally (j/release! ctx child-engine b) (j/close! ctx child-engine))))
      (finally (j/release! ctx engine a) (j/close! ctx engine)))))
(deftest zero-replicate-releases-value-and-usize-getters-use-the-scalar-lane
  (let [ctx (context)
        ctx (j/extend-program ctx (x/raw
              [(c/decl "box-index" [(c/p 1 "usize")] "object"
                 (c/let-ir 2 "object" {:box {:ty "usize" :x {:idx 1}}} (c/ret 2)))
               (c/decl "unbox-size" [(c/p 1 "object")] "usize"
                 (c/let-ir 2 "usize" {:unbox {:x {:idx 1}}}
                   ["dec" {:idx 1} 1 false false (c/ret 2)]))]))
        engine (j/machine ctx) source (j/source-binding ctx (Object.))
        [v] (j/install-graph! ctx engine
              (j/selected-owner-graph ctx source (Object.)
                [(j/graph-node ctx {:kind :ctor :id 1 :rc 1 :tag 0 :fields [42]})] [] [] [(j/graph-ref ctx 1)]))
        empty (j/call ctx engine "Array.replicate._boxed" [0 0 v])]
    (try
      (is (= 0 (size empty))) (is (= 0 (c/rc ctx v)))
      (let [a (push! ctx engine empty 7)]
        (j/retain! ctx engine a)
        (let [boxed (j/call ctx engine "Array.usize._boxed" [0 a])]
          (is (= 1 (j/call ctx engine "unbox-size" [boxed]))))
        (j/retain! ctx engine a)
        (is (= 7 (j/call ctx engine "Array.uget._boxed" [0 a (j/call ctx engine "box-index" [0]) 0])))
        (j/retain! ctx engine a)
        (is (= 7 (j/call ctx engine "Array.ugetBorrowed._boxed" [0 a (j/call ctx engine "box-index" [0]) 0])))
        (is (identical? a (j/call ctx engine "Array.uset._boxed" [0 a (j/call ctx engine "box-index" [0]) 99 0])))
        (is (= [99] (elements ctx a)))
        (j/release! ctx engine a))
      (finally (j/close! ctx engine)))))

(deftest bounds-fail-before-array-mutation-and-borrowed-primitives-require-wrappers
  (let [ctx (context)]
    (doseq [label ["Array.getInternal" "Array.getInternalBorrowed" "Array.usize" "Array.uget" "Array.ugetBorrowed"]]
      (let [engine (j/machine ctx)]
        (try
          (is (re-find #"Borrowed array primitive" (c/failure #(j/call ctx engine label []))))
          (finally (j/close! ctx engine)))))
    (let [engine (j/machine ctx) a (push! ctx engine (empty! ctx engine 2) 42)]
      (is (re-find #"Array index outside bounds" (c/failure #(j/call ctx engine "Array.set._boxed" [0 a 5 7 0]))))
      (is (= [42] (elements ctx a)))
      (is (= 1 (c/rc ctx a)))
      ;; As elsewhere, a failed execution requires explicit ownership cleanup;
      ;; it is not an import transaction or a generally recoverable guest error.
      (j/release! ctx engine a))
    (let [engine (j/machine ctx)]
      (is (re-find #"Array capacity outside bounded runtime profile"
            (c/failure #(empty! ctx engine 1000001)))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-array-checks)))
