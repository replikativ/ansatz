(ns java-ir-pointer-hash-checks
  "Bounded original FoldConsts profile, with explicit fresh target-built seeds."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [engine-support.expr :as expr] [java-ir-pointer-checks :as pointer]
            [java-ir-header-checks :as header] [java-ir-generation-checks :as g]
            [java-ir-extern-checks :as x] [java-ir-code-checks :as code]
            [java-ir-host-checks :as h] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-pointer-hash-runtime/")
(def hashes ["6b9720aa488a57b0a3698e5bde20ce1d17e178d928c9889eb1dbe9bec7784665"
             "0f6b605d51998d2e76c3dc0c14b286767f37ab8647e58005e71be810b1f5ec9a"
             "134fa49c228c361525b1760d52157bcdf494f8d7144106799145ab5a34ccc12c"])
(defn originals [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn records [] (json/read-str (slurp (str directory "execution-rows.json"))))
(defn roles [] (mapv (fn [sha] (get (first (filter #(= sha (get % "sha256")) (originals))) "label")) hashes))
(defn row [label] (get (first (filter #(= label (get % "label")) (records))) "row"))
(defn raw [label args] {:fap {:c (get (row label) "name") :ys args}})
(defn contains-wrapper []
  (c/decl "model-owned-pointer-contains" [(c/p 1 "object") (c/p 2 "object")] "uint8"
    (c/let-ir 3 "uint8" (raw ((roles) 0) [(c/v 1) (c/v 2)])
      ["dec" {:idx 2} 1 false false ["dec" {:idx 1} 1 false false (c/ret 3)]])))
(defn hash-chain [tail]
  (c/let-ir 10 "usize" (raw "ptrAddrUnsafe" ["erased" (c/v 1)])
    (c/let-ir 11 "uint64" (raw "USize.toUInt64" [(c/v 10)])
      (c/let-ir 12 "uint64" (c/lit 11)
        (c/let-ir 13 "uint64" (raw "mixHash" [(c/v 11) (c/v 12)]) tail)))))
(defn hash-model [] (c/decl "model-unauthorized-pointer-hash" [(c/p 1 "object")] "uint64"
                      (hash-chain ["dec" {:idx 1} 1 false false (c/ret 13)])))
(defn context ([] (context {}))
  ([options]
   (let [lab (binding [expr/*basis* *basis*]
               (expr/context (merge options {:extra-originals (records) :rows (concat [(contains-wrapper)] (:rows options))})))
         ctx (-> (:ctx lab) (dissoc :task-runtime) (assoc :explicit (boolean (:explicit *basis*))))]
     (assoc lab :ctx ctx :policy (j/pointer-hash-policy ctx (mapv (:headers lab) (roles)))))))
(defn engine [{:keys [ctx policy]}] (let [e (j/machine ctx)] (j/configure-pointer-hashes! ctx e policy) e))
(defn call [ctx e label args] (j/call ctx e label args))
(defn retain [ctx e value] (j/retain! ctx e value) value)
(defn fields [ctx value] (expr/fields ctx value))
(defn bvar! [ctx e n] (call ctx e "Lean.Expr.bvar._override" [n]))
(defn constant! [ctx e s] (call ctx e "Lean.Expr.const._override" [(call ctx e "Lean.Name.str._override" [0 s]) 0]))
(defn contains! [ctx e table key] (call ctx e "model-owned-pointer-contains" [(retain ctx e table) (retain ctx e key)]))
(defn insert! [ctx e table key] (call ctx e ((roles) 1) [table (retain ctx e key) 0]))
(defn seed! [ctx e] (call ctx e "Lean.Expr.FoldConstsImpl.foldUnsafe._redArg._closed_0" []))
(defn size [ctx table] (first (fields ctx table)))
(defn buckets [ctx table] (second (fields ctx table)))
(deftest finite-source-cohort-fixtures-and-policy-metadata
  (let [p (json/read-str (slurp (str directory "provenance.json")))]
    (is (= 15 (count (originals)))) (is (= 54 (count (records))))
    (is (= [] (get p "initialized-dependencies")))
    (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= (get p "execution-rows-sha256") (corpus/sha256 (str directory "execution-rows.json"))))))
(deftest default-off-entry-and-unauthorized-same-shape-body-do-not-stamp
  (let [{:keys [ctx policy] :as lab} (context {:rows [(hash-model)]}) e (j/machine ctx)
        seed (seed! ctx e) key (bvar! ctx e 0) before (mapv #(h/private-value e %) ["allocations" "stores" "retains" "releases"])]
    (is (g/bad? #(call ctx e ((roles) 0) [seed key])))
    (is (= "idle" (j/phase ctx e))) (is (nil? (pointer/metadata key)))
    (is (= before (mapv #(h/private-value e %) ["allocations" "stores" "retains" "releases"])))
    (j/configure-pointer-hashes! ctx e policy)
    (is (g/bad? #(call ctx e "model-unauthorized-pointer-hash" [key])))
    (is (= "idle" (j/phase ctx e))) (is (nil? (pointer/metadata key)))
    (is (= 1 (c/rc ctx key))) (is (g/bad? #(j/configure-pointer-hashes! ctx e policy)))
    (j/release! ctx e seed) (j/release! ctx e key) (j/close! ctx e)))
(deftest original-pointer-table-distinguishes-aliases-and-equal-allocations
  (let [{:keys [ctx] :as lab} (context) e (engine lab) seed (seed! ctx e)
        a (bvar! ctx e 0) b (bvar! ctx e 0) table (insert! ctx e seed a)]
    (is (= 1 (size ctx table))) (is (= 1 (contains! ctx e table a))) (is (= 0 (contains! ctx e table b)))
    (is (not= (pointer/word a) (pointer/word b)))
    (let [table (insert! ctx e table a) table (insert! ctx e table b) original-seed (seed! ctx e)]
      (is (= 2 (size ctx table))) (is (= 1 (contains! ctx e table a) (contains! ctx e table b)))
      (is (= 0 (size ctx original-seed)))
      (is (= 2 (c/rc ctx a) (c/rc ctx b)))
      (doseq [v [table original-seed a b]] (j/release! ctx e v)) (j/close! ctx e))))
(deftest original-insertion-forces-real-expansion-and-keeps-every-key
  (let [{:keys [ctx] :as lab} (context) e (engine lab) initial (seed! ctx e) capacity (.arraySize (buckets ctx initial))
        keys (mapv #(bvar! ctx e %) (range 144)) table (reduce #(insert! ctx e %1 %2) initial keys)]
    (is (= 144 (size ctx table))) (is (> (.arraySize (buckets ctx table)) capacity))
    (is (every? #(= 1 (contains! ctx e table %)) keys))
    (is (= 0 (size ctx (let [s (seed! ctx e)] (j/release! ctx e s) s))))
    (j/release! ctx e table) (doseq [key keys] (is (= 1 (c/rc ctx key))) (j/release! ctx e key)) (j/close! ctx e)))
(deftest genuine-get-used-constants-traversal-name-dedup-and-empty-seed-reuse
  (let [{:keys [ctx] :as lab} (context) e (engine lab) a (constant! ctx e "A") b (constant! ctx e "B")
        a2 (constant! ctx e "A") sub (call ctx e "Lean.Expr.app._override" [(retain ctx e a) (retain ctx e b)])
        input (call ctx e "Lean.Expr.app._override" [(retain ctx e sub) (call ctx e "Lean.Expr.app._override" [sub a2])])]
    (dotimes [_ 2]
      (let [names (call ctx e "Lean.Expr.getUsedConstants" [(retain ctx e input)])
            live (take (.arraySize names) (fields ctx names))]
        (is (= ["A" "B"] (mapv #(second (fields ctx %)) live))) (j/release! ctx e names)))
    (let [empty (seed! ctx e)] (is (= 0 (size ctx empty))) (j/release! ctx e empty))
    (doseq [v [input a b]] (j/release! ctx e v)) (j/close! ctx e)))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-pointer-hash-checks)))
