(ns java-ir-expr-full-native-checks
 "Owned original native530 entry; source acceptance is external to model Headers."
 (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-full-checks :as full] [java-ir-expr-full-control-checks :as control]
  [java-ir-expr-machinery-checks :as expr] [java-ir-expr-direct-checks :as direct]
  [java-ir-expr-find-checks :as find] [java-ir-level-mvars-checks :as level]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-sync-task-checks :as sync] [java-ir-continuation-checks :as k]
  [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-full-native-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(def raw "Lean.instantiateExprMVarsImp")
(def boxed "Lean.instantiateExprMVarsImp._boxed")
(defn model-rows []
 [(c/decl "model-native-ap" (mapv #(c/p % "object") [1 2 3]) "object"
   (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
  (c/decl "model-native-partial-ap" (mapv #(c/p % "object") [1 2]) "object"
   (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
  (c/decl "model-native-pap" [(c/p 1 "object")] "object"
   (c/let-ir 2 "object" {:pap {:c (get-in (first (records)) ["row" "name"]) :ys [(c/v 1)]}} (c/ret 2)))
  (c/decl "model-native-fap" (mapv #(c/p % "object") [1 2]) "object"
   (c/let-ir 3 "object" {:fap {:c (get-in (first (records)) ["row" "name"]) :ys [(c/v 1) (c/v 2)]}} (c/ret 3)))])
(defn context
 ([] (context {}))
 ([options]
  (let [models (model-rows) model-labels #{"model-native-ap" "model-native-partial-ap" "model-native-pap" "model-native-fap"}
        options (-> options (update :rows #(concat models %)) (update :defer #(into model-labels %)))
        lab (binding [full/*basis* *basis*] (full/context options))
        source (:source lab) rs (records)
        hs (into {} (for [r rs] [(get r "label") (j/declaration-header source (get r "row") (get r "sha256"))]))
        headers (merge (:headers lab) hs) rows (merge (:rows lab) (into {} (map (juxt #(get % "label") #(get % "row")) rs)))
        ctx (j/register-headers (:ctx lab) (vec (vals hs)))
        by-name (into {} (for [[label header] headers] [(get (rows label) "name") header]))
        wrapper (second rs) ctx (j/materialize-body ctx (hs boxed) (get wrapper "row") (mapv by-name (find/direct (get wrapper "row"))))
        ctx (reduce (fn [ctx label] (j/materialize-body ctx (headers label) (rows label) (mapv by-name (find/direct (rows label))))) ctx model-labels)]
   (assoc lab :ctx ctx :headers headers :rows rows))))
(defn policy [{:keys [ctx level-policy headers]}]
 (j/expr-instantiation-policy ctx level-policy (mapv headers direct/helpers) (mapv headers expr/roles)))
(defn engine [lab]
 (let [e (full/engine lab)] (j/configure-expr-instantiation! (:ctx lab) e (policy lab)) e))
(defn call [ctx e label args] (j/start! ctx e label args) (sync/finish! ctx e))

(deftest authentic-two-rows-have-owned-boxed-abi
 (let [rs (records)]
  (is (= 2 (count rs)))
  (is (= ["7e53092b477181a60a5e66f6cf2e2f33827b9f05411b294359b860431fc8a9ef"
          "753b7adf308815b5c9585ff8e19abd6a1064fc78ef7dfe57b4a97001f67435a5"] (mapv #(get % "sha256") rs)))
  (doseq [r rs :let [d (first (vals (get-in r ["row" "ir"])) )]]
   (is (= ["object" "object"] (mapv #(get % "ty") (get d "xs"))))
   (is (= [false false] (mapv #(get % "borrow") (get d "xs"))))
   (is (= "object" (get d "type"))))))

(deftest raw-boxed-fap-pap-and-ap-all-return-the-original-pair-contract
 (doseq [mode [:raw :boxed :fap :pap :ap]]
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (level/fresh! ctx e)
        input (expr/bvar! ctx e 0)
        pair (case mode
          :raw (call ctx e raw [m input]) :boxed (call ctx e boxed [m input])
          :fap (call ctx e "model-native-fap" [m input])
          :pap (call ctx e "model-native-partial-ap" [(call ctx e "model-native-pap" [m]) input])
          :ap (call ctx e "model-native-ap" [(j/make-closure! ctx e raw []) m input]))]
   (is (= 2 (count (expr/fields ctx pair))))
   (is (identical? m (first (expr/fields ctx pair))))
   (is (identical? input (full/full-result ctx pair)))
   (is (= 1 (c/rc ctx input))) (full/close! ctx e pair))))

(deftest default-and-inactive-raw-entry-reject-before-native-claims
 (doseq [inactive? [false true]]
  (let [{:keys [ctx] :as lab} (context (if inactive? {:inactive true} {})) e (j/machine ctx)
        m (level/fresh! ctx e) input (expr/bvar! ctx e 0) before (k/counters ctx e)]
   (is (g/bad? #(j/start! ctx e raw [m input])))
   (is (= "idle" (j/phase ctx e))) (is (= before (k/counters ctx e)))
   (is (= 1 (c/rc ctx m) (c/rc ctx input)))
   (if inactive? (do (j/release! ctx e m) (j/release! ctx e input) (j/close! ctx e))
       (do (sync/release! ctx e m) (sync/release! ctx e input) (sync/close! ctx e))))))

(deftest actual-level-policy-identity-and-once-only-configuration
 (let [{:keys [ctx headers] :as lab} (context) e (full/engine lab)
       equal-policy (apply j/level-instantiation-policy ctx (map headers level/roles))
       different (j/expr-instantiation-policy ctx equal-policy (mapv headers direct/helpers) (mapv headers expr/roles))]
  (is (g/bad? #(j/configure-expr-instantiation! ctx e different)))
  (is (nil? (expr/private-value e "exprInstantiationPolicy")))
  (j/configure-expr-instantiation! ctx e (policy lab))
  (is (g/bad? #(j/configure-expr-instantiation! ctx e (policy lab))))
  (sync/close! ctx e)))

(deftest raw-input-alias-undercredit-rejects-without-start-or-ap-consumption
 (doseq [ap? [false true]]
  (let [{:keys [ctx] :as lab} (context) e (engine lab) value (expr/bvar! ctx e 0)
        closure (when ap? (j/make-closure! ctx e raw [])) before (k/counters ctx e)]
   (if ap?
    (do (is (g/bad? #(call ctx e "model-native-ap" [closure value value])))
        (is (not (true? (expr/private-value closure "dead"))))
        (is (= 1 (c/rc ctx closure))))
    (do (is (g/bad? #(j/start! ctx e raw [value value]))) (is (= "idle" (j/phase ctx e)))))
   (is (= 1 (c/rc ctx value)))
   ;; AP caller legitimately entered; its instruction accounting need not roll back.
   (when-not ap? (is (= before (k/counters ctx e))))
   (when-not ap? (sync/release! ctx e value) (sync/close! ctx e)))))

(deftest native-entry-preserves-outer-instruction-accounting-and-forked-policy
 (let [{:keys [ctx] :as lab} (context) parent (engine lab)
       {child :engine} (j/fork! ctx parent [])]
  (is (identical? (expr/private-value parent "exprInstantiationPolicy") (expr/private-value child "exprInstantiationPolicy")))
  (doseq [e [parent child]]
   (let [m (level/fresh! ctx e) input (expr/bvar! ctx e 0)]
    (j/start! ctx e "model-native-fap" [m input]) (j/advance! ctx e 1)
    (is (= 1 (j/instructions ctx e))) (is (some? (full/state e)))
    (let [pair (sync/finish! ctx e)]
     (is (> (j/instructions ctx e) 1)) (full/close! ctx e pair))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-full-native-checks)))
