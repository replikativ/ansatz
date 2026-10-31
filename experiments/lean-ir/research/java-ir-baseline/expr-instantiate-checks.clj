(ns java-ir-expr-instantiate-checks
 "Original six borrowed pure transforms; constructor bodies remain authentic."
 (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-machinery-checks :as expr] [java-ir-array-checks :as arr]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-sync-task-checks :as sync] [java-ir-continuation-checks :as k]
  [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-instantiate-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(def names ["instantiate" "instantiate1" "instantiateRange" "instantiateRev" "instantiateRevRange" "liftLooseBVars"])
(defn label [op] (str "Lean.Expr." op "._boxed"))
(defn context
 ([] (context {}))
 ([options] (binding [expr/*basis* *basis*]
   (expr/context (update options :extra-originals #(concat (records) (arr/originals) %))))))
(defn machine [{:keys [ctx headers]}]
 (let [e (j/machine ctx)]
  (j/configure-expr-transforms! ctx e (j/expr-transform-policy ctx (mapv headers expr/roles))) e))
(defn call [ctx e name xs] (j/start! ctx e name xs) (sync/finish! ctx e))
(defn apply! [ctx e op xs] (call ctx e (label op) xs))
(defn array! [ctx e xs]
 (reduce #(call ctx e "Array.push._boxed" [0 %1 %2])
  (call ctx e "Array.mkEmpty._boxed" [0 (long (count xs))]) xs))
(defn index [ctx x] (first (expr/fields ctx x)))
(defn dead? [x] (true? (h/private-value x "dead")))
(defn state [e]
 (loop [a (sync/action e)]
  (when a (or (h/private-value a "exprMachinery") (recur (h/private-value a "parent"))))))
(defn job [e] (some-> (state e) (h/private-value "jobs") ^java.util.Deque (.peekLast)))
(defn until! [ctx e predicate]
 (loop [n 100000]
  (assert (pos? n) "Bounded pure transform checkpoint")
  (when-not (predicate) (assert (= "running" (j/phase ctx e)))
   (j/advance! ctx e 1) (recur (dec n)))))
(defn release-close! [ctx e x] (sync/release! ctx e x) (sync/close! ctx e))

(deftest authenticated-six-raw-and-six-owning-wrappers
 (let [rs (records) p (json/read-str (slurp (str directory "provenance.json")))]
  (is (= 12 (count rs)))
  (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
  (is (= [63 112160 []] (mapv p ["helper-closure-rows" "helper-closure-bytes" "initialized-dependencies"])))
  (doseq [r rs :let [d (or (get-in r ["row" "ir" "extern"]) (get-in r ["row" "ir" "fdecl"]))
                    raw? (some? (get-in r ["row" "ir" "extern"]))]]
   (is (= "object" (get d "type")))
   (is (every? #(= raw? (get % "borrow")) (get d "xs"))))))

(deftest forward-reverse-and-borrowed-single-use-distinct-array-order
 (doseq [[op n expected] [["instantiate" 0 10] ["instantiate" 1 20]
                           ["instantiateRev" 0 20] ["instantiateRev" 1 10]
                           ["instantiate" 4 2] ["instantiateRev" 4 2]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e n)
        values (array! ctx e [(expr/bvar! ctx e 10) (expr/bvar! ctx e 20)])
        out (apply! ctx e op [input values])]
   (is (= expected (index ctx out))) (is (dead? input)) (is (dead? values))
   (is (= 1 (c/rc ctx out))) (release-close! ctx e out)))
 (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e 0)
       replacement (expr/bvar! ctx e 7) out (apply! ctx e "instantiate1" [input replacement])]
  (is (identical? replacement out)) (is (dead? input)) (is (= 1 (c/rc ctx out))) (release-close! ctx e out)))

(deftest slices-use-selected-array-direction-not-loose-variable-cutoff
 (doseq [[op n expected] [["instantiateRange" 0 10] ["instantiateRange" 1 20]
  ["instantiateRevRange" 0 20] ["instantiateRevRange" 1 10] ["instantiateRange" 4 2]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        values (array! ctx e (mapv #(expr/bvar! ctx e %) [99 10 20 88]))
        out (apply! ctx e op [(expr/bvar! ctx e n) 1 3 values])]
   (is (= expected (index ctx out))) (is (dead? values)) (release-close! ctx e out))))

(deftest forward-empty-identity-reverse-empty-rebuild-and-closed-identity
 (doseq [op ["instantiate" "instantiateRev" "instantiateRange" "instantiateRevRange"]
         closed? [false true]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        input (if closed? (expr/sort! ctx e) (expr/bvar! ctx e 0))
        values (array! ctx e []) range? (.contains ^String op "Range")
        out (apply! ctx e op (if range? [input 0 0 values] [input values]))
        same? (or closed? (not (.contains ^String op "Rev")))]
   (is (= same? (identical? input out)))
   (is (= (not same?) (dead? input)))
   (when-not closed? (is (= 0 (index ctx out)))) (release-close! ctx e out))))

(deftest substitution-lifts-open-values-under-binders
 (doseq [op ["instantiate1" "instantiate" "instantiateRev"]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        input (expr/lam! ctx e (expr/app! ctx e (expr/bvar! ctx e 0) (expr/bvar! ctx e 1)))
        replacement (expr/bvar! ctx e 0)
        out (apply! ctx e op [input (if (= op "instantiate1") replacement (array! ctx e [replacement]))])
        [bound inserted] (expr/fields ctx (nth (expr/fields ctx out) 2))]
   (is (= 0 (index ctx bound))) (is (= 1 (index ctx inserted)))
   (is (dead? input)) (release-close! ctx e out))))

(deftest lift-unsigned32-narrowing-and-canonical-heap-identity
 (doseq [[s d expected same?] [[0 2 2 false] [1 2 0 true]
                              [4294967296 2 2 false] [0 4294967296 0 true]
                              [4294967297 2 0 true]
                              [(.shiftLeft java.math.BigInteger/ONE 80) 2 0 true]
                              [0 (.shiftLeft java.math.BigInteger/ONE 80) 0 true]
                              [(java.math.BigInteger/valueOf 0) (java.math.BigInteger/valueOf 3) 3 false]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e 0)
        out (apply! ctx e "liftLooseBVars" [input s d])]
   (is (= expected (index ctx out))) (is (= same? (identical? input out)))
   (is (= 1 (c/rc ctx out))) (release-close! ctx e out))))

(deftest invalid-slices-are-checked-even-for-closed-input-before-native-claims
 (doseq [[b end] [[-1 0] [2 1] [0 2] [0 (.shiftLeft java.math.BigInteger/ONE 80)]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/sort! ctx e)
        values (array! ctx e [(expr/bvar! ctx e 0)]) before (k/counters ctx e)]
   (is (g/bad? #(apply! ctx e "instantiateRange" [input b end values])))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input) (c/rc ctx values)))
   (is (= "failed" (j/phase ctx e))))))

(deftest raw-root-and-closure-entry-fences-preserve-credits
 (doseq [op names]
  (let [{:keys [ctx source headers] :as lab} (context) e (machine lab)
        raw (str "Lean.Expr." op) input (expr/bvar! ctx e 0) values (array! ctx e [])
        args (case op "instantiate1" [input input] "liftLooseBVars" [input 0 0]
               ("instantiateRange" "instantiateRevRange") [input 0 0 values] [input values])
        before (k/counters ctx e)]
   (is (g/bad? #(j/start! ctx e raw args))) (is (= "idle" (j/phase ctx e)))
   (is (g/bad? #(j/make-closure! ctx e raw [])))
   (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
    [(j/graph-node ctx {:kind :closure :id 1 :target (headers raw)})] [] [] [(j/graph-ref ctx 1)]))))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input) (c/rc ctx values)))
   (sync/release! ctx e values) (release-close! ctx e input))))

(deftest paused-borrowed-slice-fork-remaps-array-and-input
 (let [{:keys [ctx] :as lab} (context) parent (machine lab)
       input (expr/lam! ctx parent (expr/bvar! ctx parent 1))
       values (array! ctx parent [(expr/bvar! ctx parent 3)])]
  (j/start! ctx parent (label "instantiateRev") [input values])
  (until! ctx parent #(some-> (job parent) (h/private-value "slice")))
  (let [{child :engine} (j/fork! ctx parent []) cj (job child)
        child-input (h/private-value cj "input")
        child-array (h/private-value (h/private-value cj "slice") "array")]
   (is (not (identical? input child-input))) (is (not (identical? values child-array)))
   (doseq [e [child parent]]
    (let [out (sync/finish! ctx e)]
     (is (= 4 (index ctx (nth (expr/fields ctx out) 2)))) (release-close! ctx e out)))
   (is (dead? input)) (is (dead? values)) (is (dead? child-input)) (is (dead? child-array)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-instantiate-checks)))

(deftest reverse-empty-under-binders-rebuilds-only-loose-subtrees
 (doseq [idx [0 1]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab)
        input (expr/lam! ctx e (expr/bvar! ctx e idx))
        out (apply! ctx e "instantiateRev" [input (array! ctx e [])])]
   (is (= (zero? idx) (identical? input out)))
   (is (= idx (index ctx (nth (expr/fields ctx out) 2))))
   (release-close! ctx e out))))

(deftest lift-result-boundary-is-exact-and-large-delta-retains-failed-owners
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       out (apply! ctx e "liftLooseBVars" [(expr/bvar! ctx e 0) 0 1048574])]
  (is (= 1048574 (index ctx out))) (release-close! ctx e out))
 (doseq [delta [1048575 4294967295]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (expr/bvar! ctx e 0)]
   (is (re-find #"bvar constructor range" (c/failure #(apply! ctx e "liftLooseBVars" [input 0 delta]))))
   (is (= "failed" (j/phase ctx e))) (is (= 1 (c/rc ctx input)))
   (is (not (dead? input))) (is (some? (state e)))
   (is (g/bad? #(j/fork! ctx e []))))))

(deftest selected-small-biginteger-range-and-unused-live-elements
 ;; Small exact BigInteger is a typed Nat model, not proof of a native MPZ tag.
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       values (array! ctx e [(expr/bvar! ctx e 99) (expr/bvar! ctx e 7) (expr/bvar! ctx e 88)])
       out (apply! ctx e "instantiateRevRange" [(expr/bvar! ctx e 0)
        (java.math.BigInteger/valueOf 1) (java.math.BigInteger/valueOf 2) values])]
  (is (= 7 (index ctx out))) (is (= 1 (c/rc ctx out)))
  (is (dead? values)) (release-close! ctx e out)))

(deftest original-constructors-can-demand-code-and-fork-in-nested-lift
 (doseq [role [0 4]]
  (let [target (expr/roles role) {:keys [ctx] :as lab} (context {:defer #{target}})
        parent (machine lab) input (expr/lam! ctx parent (expr/bvar! ctx parent 1))
        values (array! ctx parent [(expr/bvar! ctx parent 3)])]
   (j/start! ctx parent (label "instantiate") [input values])
   (loop [n 10000]
    (assert (pos? n))
    (when (= "running" (j/phase ctx parent)) (j/advance! ctx parent 1) (recur (dec n))))
   (is (= "code-call" (j/phase ctx parent)))
   (let [request (j/code-request ctx parent) {child :engine} (j/fork! ctx parent [])
         ready (expr/materialize lab target)]
    (is (identical? (get-in lab [:headers target]) (j/request-value request "header")))
    (doseq [e [parent child]]
     (j/install-program! ready e) (j/resume-code! ready e (j/code-request ready e))
     (let [out (sync/finish! ready e)]
      (is (= 4 (index ready (nth (expr/fields ready out) 2)))) (release-close! ready e out)))))))

(deftest offset-cache-distinguishes-shared-node-binder-depth
 (let [{:keys [ctx] :as lab} (context) e (machine lab) shared (expr/bvar! ctx e 1)
       input (expr/app! ctx e (expr/retain ctx e shared) (expr/lam! ctx e shared))
       values (array! ctx e [(expr/bvar! ctx e 5)])
       out (apply! ctx e "instantiate" [input values])
       [f lam] (expr/fields ctx out) body (nth (expr/fields ctx lam) 2)]
  (is (= 0 (index ctx f))) (is (= 6 (index ctx body)))
  (is (not (identical? f body))) (is (dead? shared))
  (is (= 1 (c/rc ctx f) (c/rc ctx body))) (release-close! ctx e out)))
