(ns java-ir-expr-loose-checks
 "Borrowed atomic loose search and resumable original lowering."
 (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-machinery-checks :as expr] [java-ir-expr-instantiate-checks :as pure]
  [java-ir-sync-task-checks :as sync] [java-ir-host-checks :as h]
  [java-ir-generation-checks :as g] [java-ir-continuation-checks :as k]
  [java-ir-logical-sharing-checks :as sharing] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-loose-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn named [label] (first (filter #(= label (get % "label")) (records))))
(defn model-rows []
 [(c/decl "model-has-borrow" [(assoc (c/p 1 "object") :borrow true) (assoc (c/p 2 "tobject") :borrow true)] "uint8"
    (c/let-ir 3 "uint8" {:fap {:c (get-in (named "Lean.Expr.hasLooseBVar") ["row" "name"]) :ys [(c/v 1) (c/v 2)]}} (c/ret 3)))])
(defn context
 ([] (context {}))
 ([options] (binding [expr/*basis* *basis*]
  (expr/context (-> options (update :rows #(concat (model-rows) %))
                  (update :extra-originals #(concat (records) %)))))))
(defn query-context []
 (let [lab (context {:inactive true})] (assoc lab :ctx (assoc (:ctx lab) :explicit (boolean (:explicit *basis*))))))
(defn machine [lab] (pure/machine lab))
(defn bvar! [ctx e index] (j/call ctx e (str "model-setup-" (expr/roles 0)) [index]))
(defn sort! [ctx e] (j/call ctx e (str "model-setup-" (expr/roles 1)) [0]))
(defn app! [ctx e f a] (j/call ctx e (str "model-setup-" (expr/roles 3)) [f a]))
(defn lam! [ctx e body] (j/call ctx e (str "model-setup-" (expr/roles 4)) [0 (sort! ctx e) body 0]))
(defn has? [ctx e input i] (j/call ctx e "model-has-borrow" [input i]))
(defn lower! [ctx e input s d] (pure/call ctx e "Lean.Expr.lowerLooseBVars._boxed" [input s d]))
(defn cleanup! [ctx e value] (j/release! ctx e value) (j/close! ctx e))

(deftest authentic-four-rows-and-bounded-helper-closure
 (let [p (json/read-str (slurp (str directory "provenance.json")))]
  (is (= 4 (count (records))))
  (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
  (is (= [55 [] false] (mapv p ["helper-closure-rows" "initialized-dependencies" "quickLt-enabled-by-this-unit"])))
  (doseq [r (records) :let [d (first (vals (get-in r ["row" "ir"])))
                          raw? (contains? (get-in r ["row" "ir"]) "extern")]]
   (is (every? #(= raw? (get % "borrow")) (get d "xs"))))))

(deftest has-loose-searches-partial-app-and-preserves-readonly-credits
 (let [{:keys [ctx]} (query-context) e (j/machine ctx)
       input (app! ctx e (bvar! ctx e 0) (bvar! ctx e 2)) before (k/counters ctx e)]
  (is (= [1 0 1 0] (mapv #(has? ctx e input %) [0 1 2 3])))
  (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
  (cleanup! ctx e input)))

(deftest has-loose-binder-and-let-body-offsets
 (doseq [[index expected] [[0 [0 0 0]] [1 [1 0 0]] [2 [0 1 0]]]]
  (let [{:keys [ctx]} (query-context) e (j/machine ctx) input (lam! ctx e (bvar! ctx e index))]
   (is (= expected (mapv #(has? ctx e input %) [0 1 2]))) (cleanup! ctx e input)))
 (let [{:keys [ctx]} (query-context) e (j/machine ctx)
       input (j/call ctx e (str "model-setup-" (expr/roles 6)) [0 (sort! ctx e) (bvar! ctx e 0) (bvar! ctx e 3) 1])]
  (is (= [1 0 1 0] (mapv #(has? ctx e input %) [0 1 2 3]))) (cleanup! ctx e input)))

(deftest has-loose-canonical-nat-and-uint32-wrap-domain
 (let [{:keys [ctx]} (query-context) e (j/machine ctx) zero (bvar! ctx e 0) one (bvar! ctx e 1)
       heap (.shiftLeft java.math.BigInteger/ONE 100)]
  (is (= [1 0 0 0 1] (mapv #(has? ctx e zero %) [4294967296 4294967297 Long/MAX_VALUE heap (java.math.BigInteger/valueOf 0)])))
  (is (= [0 1] (mapv #(has? ctx e one %) [4294967296 4294967297])))
  (j/release! ctx e zero) (cleanup! ctx e one)))

(deftest shared-same-node-different-offset-is-not-a-global-visited-bit
 (let [{:keys [ctx]} (query-context) e (j/machine ctx) shared (bvar! ctx e 1)
       input (app! ctx e (j/call ctx e (str "model-setup-" (expr/roles 4)) [0 (sort! ctx e) (do (j/retain! ctx e shared) shared) 0]) shared)]
  (is (= 1 (has? ctx e input 0))) (is (= 1 (has? ctx e input 1)))
  (is (= 0 (has? ctx e input 2))) (cleanup! ctx e input)))

(deftest original-owning-query-wrapper-returns-bool-and-releases-input
 (let [{:keys [ctx]} (query-context) e (j/machine ctx) input (bvar! ctx e 3)]
  (is (= 1 (j/call ctx e "Lean.Expr.hasLooseBVar._boxed" [input 3])))
  (is (true? (h/private-value input "dead"))) (j/close! ctx e)))

(deftest lower-full-width-check-precedes-narrowing-and-source-shortcuts
 (doseq [[s d expected same?] [[3 2 3 false] [6 2 5 true] [0 0 5 true] [1 2 5 true]
          [1 4294967297 5 true] [4294967299 2 3 false] [4294967298 4294967297 4 false]
          [0 (.shiftLeft java.math.BigInteger/ONE 80) 5 true]
          [(.shiftLeft java.math.BigInteger/ONE 80) 1 5 true]
          [(java.math.BigInteger/valueOf 3) (java.math.BigInteger/valueOf 2) 3 false]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (bvar! ctx e 5)
        out (lower! ctx e input s d)]
   (is (= [expected] (expr/fields ctx out))) (is (= same? (identical? input out)))
   (is (= 1 (c/rc ctx out))) (sync/release! ctx e out) (sync/close! ctx e))))

(deftest lower-narrowed-assertion-domain-rejects-only-after-identity-shortcuts
 (let [{:keys [ctx] :as lab} (context) e (machine lab) input (bvar! ctx e 0) before (k/counters ctx e)]
  (is (re-find #"narrowed assertion domain" (c/failure #(lower! ctx e input 4294967296 1))))
  (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
  (is (= "failed" (j/phase ctx e))))
 (doseq [[closed? d] [[true 1] [false 4294967296]]]
  (let [{:keys [ctx] :as lab} (context) e (machine lab) input (if closed? (sort! ctx e) (bvar! ctx e 0))
        out (lower! ctx e input 4294967296 d)]
   (is (identical? input out)) (sync/release! ctx e out) (sync/close! ctx e))))

(deftest lower-under-binders-preserves-bound-indices-and-lowers-only-selected-ones
 (let [{:keys [ctx] :as lab} (context) e (machine lab)
       input (lam! ctx e (app! ctx e (bvar! ctx e 0) (bvar! ctx e 4)))
       out (lower! ctx e input 3 2) body (nth (expr/fields ctx out) 2)]
  (is (= [[0] [2]] (mapv #(expr/fields ctx %) (expr/fields ctx body))))
  (is (true? (h/private-value input "dead"))) (sync/release! ctx e out) (sync/close! ctx e)))

(deftest lowering-constructor-code-pause-forks-the-existing-owner-packets
 (let [target (expr/roles 0) {:keys [ctx] :as lab} (context {:defer #{target}}) parent (machine lab)
       input (bvar! ctx parent 5)]
  (j/start! ctx parent "Lean.Expr.lowerLooseBVars._boxed" [input 3 2])
  (loop [n 10000] (assert (pos? n))
   (when (= "running" (j/phase ctx parent)) (j/advance! ctx parent 1) (recur (dec n))))
  (is (= "code-call" (j/phase ctx parent)))
  (let [{child :engine} (j/fork! ctx parent []) ready (expr/materialize lab target)]
   (doseq [e [parent child]]
    (is (nil? (h/private-value (pure/state e) "input")))
    (j/resume-code! ready e (j/code-request ready e))
    (let [out (sync/finish! ready e)]
     (is (= [3] (expr/fields ready out))) (sync/release! ready e out) (sync/close! ready e))))))

(deftest both-raw-roots-and-makeclosure-import-fences-reject-before-credits
 (doseq [raw ["Lean.Expr.hasLooseBVar" "Lean.Expr.lowerLooseBVars"]]
  (let [{:keys [ctx source headers] :as lab} (context) e (machine lab) input (bvar! ctx e 0)
        before (k/counters ctx e) args (if (= raw "Lean.Expr.hasLooseBVar") [input 0] [input 0 0])]
   (is (g/bad? #(j/start! ctx e raw args))) (is (= "idle" (j/phase ctx e)))
   (is (g/bad? #(j/make-closure! ctx e raw [])))
   (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
     [(j/graph-node ctx {:kind :closure :id 1 :target (headers raw)})] [] [] [(j/graph-ref ctx 1)]))))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
   (sync/release! ctx e input) (sync/close! ctx e))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-loose-checks)))
