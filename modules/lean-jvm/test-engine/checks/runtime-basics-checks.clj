(ns java-ir-runtime-basics-checks
  "Bounded Nat, ready Task ownership and checked array valid paths."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as host]
            [java-ir-ref-checks :as ref] [java-ir-array-checks :as a]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(defn originals [kind] (json/read-str (slurp (str "test/fixtures/java-" kind "-runtime/original-rows.json"))))
(defn context []
  (let [rows (mapv #(get % "row") (concat (originals "nat") (originals "task")
                              (originals "array-checked") (originals "array") (ref/originals)))
        synthetic [(c/decl "fresh-value" [(c/p 1 "object")] "object"
                      (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))
                   (c/decl "fake-task" [(c/p 1 "object")] "object"
                      (c/let-ir 2 "object" (c/ctor 252 [(c/v 1)] 0) (c/ret 2)))
                   (c/decl "project" [(c/p 1 "object")] "object"
                      (c/let-ir 2 "object" {:proj {:x {:idx 1} :i 0}} (c/ret 2)))]]
    (assoc *basis* :program (j/invoke-static (:prepare *basis*) [(into rows (x/raw synthetic))]))))
(defn call [ctx engine name args] (j/call ctx engine (str name "._boxed") args))
(defn fresh [ctx engine] (j/call ctx engine "fresh-value" [0]))
(defn pure [ctx engine value] (call ctx engine "Task.pure" [0 value]))
(defn get-task [ctx engine task] (call ctx engine "Task.get" [0 task]))
(def huge (.shiftLeft java.math.BigInteger/ONE 80))
(defn carrier [value] (if (<= value Long/MAX_VALUE) (long value) (biginteger value)))

(deftest exact-original-fixtures-and-abis
  (doseq [[kind n] [["nat" 10] ["task" 4] ["array-checked" 4]]
          :let [manifest (edn/read-string (slurp (str "test/fixtures/java-" kind "-runtime/provenance.edn")))
                rows (originals kind)]]
    (is (= n (count rows)))
    (is (= (:fixture-sha256 manifest) (corpus/sha256 (str "test/fixtures/java-" kind "-runtime/original-rows.json"))))
    (doseq [r rows :when (get-in r ["row" "ir" "extern"])]
      (is (string? (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi"
                                                (into-array Class [java.util.Map])) [(get r "row")]))))))

(deftest nat-comparison-bitwise-and-log2-preserve-magnitude
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [x [0 1 7 Long/MAX_VALUE huge] y [0 1 7 Long/MAX_VALUE huge]]
        (is (= (if (<= x y) 1 0) (call ctx engine "Nat.decLe" [x y])))
        (is (= (.or (biginteger x) (biginteger y)) (call ctx engine "Nat.lor" [x y]))))
      (doseq [power [0 1 2 8 62 63 64 128]
              delta [-1 0 1]
              :let [v (.add (.shiftLeft java.math.BigInteger/ONE power) (biginteger delta))]]
        (is (= (max 0 (dec (.bitLength v))) (call ctx engine "Nat.log2" [(carrier v)]))))
      (finally (j/close! ctx engine)))))

(deftest nat-shifts-handle-zero-and-huge-exponents-before-narrowing
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [value [0 1 7 Long/MAX_VALUE huge] exponent [0 1 4 63 64 128]]
        (is (= (.shiftLeft (biginteger value) exponent) (call ctx engine "Nat.shiftLeft" [value exponent])))
        (is (= (.shiftRight (biginteger value) exponent) (call ctx engine "Nat.shiftRight" [value exponent]))))
      (is (= 0 (call ctx engine "Nat.shiftLeft" [0 huge])))
      (is (= 0 (call ctx engine "Nat.shiftRight" [huge huge])))
      (finally (j/close! ctx engine))))
  (let [ctx (context) engine (j/machine ctx)]
    (is (re-find #"Nat.shiftLeft result outside bounded runtime bit limit"
                 (c/failure #(call ctx engine "Nat.shiftLeft" [1 huge]))))))

(deftest ready-task-unique-shared-nested-and-unobserved-owner-transfers
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (let [v (fresh ctx engine) task (pure ctx engine v)]
        (is (= 1 (c/rc ctx v) (c/rc ctx task)))
        (is (identical? v (get-task ctx engine task)))
        (is (= 1 (c/rc ctx v))) (is (host/private-value task "dead"))
        (j/release! ctx engine v))
      (let [v (fresh ctx engine) task (pure ctx engine v)]
        (j/retain! ctx engine task)
        (is (identical? v (get-task ctx engine task)))
        (is (= 2 (c/rc ctx v))) (is (= 1 (c/rc ctx task)))
        (j/release! ctx engine v) (is (= 1 (c/rc ctx v)))
        (j/release! ctx engine task) (is (= 0 (c/rc ctx v))))
      (let [v (fresh ctx engine) inner (pure ctx engine v) outer (pure ctx engine inner)]
        (is (identical? inner (get-task ctx engine outer)))
        (is (= 1 (c/rc ctx inner)))
        (is (identical? v (get-task ctx engine inner)))
        (j/release! ctx engine v) (is (= 0 (c/rc ctx v))))
      (let [v (fresh ctx engine) task (pure ctx engine v)]
        (j/release! ctx engine task) (is (= 0 (c/rc ctx v))))
      (finally (j/close! ctx engine)))))

(deftest ready-task-fork-preserves-aliased-ref-payloads-and-branch-isolation
  (let [ctx (context) engine (j/machine ctx)
        cell (ref/make-ref! ctx engine 42) task (pure ctx engine cell)
        child (j/fork! ctx engine [task]) child-engine (:engine child) child-task (first (:roots child))]
    (try
      (let [parent-cell (get-task ctx engine task) child-cell (get-task ctx child-engine child-task)]
        (is (identical? cell parent-cell)) (is (not (identical? cell child-cell)))
        (is (= 1 (c/rc ctx parent-cell) (c/rc ctx child-cell)))
        (ref/ref-set! ctx child-engine child-cell 99)
        (is (= 42 (ref/ref-get! ctx engine parent-cell)))
        (is (= 99 (ref/ref-get! ctx child-engine child-cell)))
        (j/release! ctx engine parent-cell) (j/release! ctx child-engine child-cell))
      (finally (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest task-kind-is-not-an-arbitrary-constructor-or-tag
  (let [ctx (context)]
    (doseq [make-value [#(fresh ctx %) #(j/call ctx % "fake-task" [42])]]
      (let [engine (j/machine ctx) v (make-value engine)]
        (is (re-find #"Expected engine ready Task" (c/failure #(get-task ctx engine v))))
        (is (= 1 (c/rc ctx v)))
        (j/release! ctx engine v)))
    (let [engine (j/machine ctx) task (pure ctx engine 42)]
      (is (re-find #"not a constructor" (c/failure #(j/call ctx engine "project" [task]))))
      (is (= 1 (c/rc ctx task))) (j/release! ctx engine task))))

(deftest checked-getters-keep-default-borrowed-and-distinguish-owned-results
  (let [ctx (context) engine (j/machine ctx) v (fresh ctx engine) default (fresh ctx engine)
        array (a/push! ctx engine (a/empty! ctx engine 4) v)]
    (try
      (j/retain! ctx engine default) (j/retain! ctx engine array)
      (is (identical? v (call ctx engine "Array.get!Internal" [0 default array 0])))
      (is (= 2 (c/rc ctx v))) (is (= 1 (c/rc ctx default)))
      (j/release! ctx engine v)
      (j/retain! ctx engine default) (j/retain! ctx engine array)
      (is (identical? v (call ctx engine "Array.get!InternalBorrowed" [0 default array 0])))
      (is (= 1 (c/rc ctx v) (c/rc ctx default)))
      (finally (j/release! ctx engine default) (j/release! ctx engine array) (j/close! ctx engine)))))

(deftest checked-get-panic-path-rejects-before-producing-a-fake-default
  (let [ctx (context) engine (j/machine ctx) default (fresh ctx engine)
        array (a/empty! ctx engine 4)]
    (is (re-find #"Array.get! panic path outside bounded runtime profile"
          (c/failure #(call ctx engine "Array.get!InternalBorrowed" [0 default array huge]))))
    (is (= 1 (c/rc ctx default) (c/rc ctx array)))
    (j/release! ctx engine default) (j/release! ctx engine array)))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-runtime-basics-checks)))
