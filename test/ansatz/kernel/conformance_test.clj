(ns ansatz.kernel.conformance-test
  "Conformance harness for the TWO kernels (RETHINK Item 5c). ansatz has two independent kernel
   implementations over the SAME Java `Expr` objects: the Clojure tactic-kernel (ansatz.kernel.tc /
   ansatz.kernel.reduce — used during elaboration/tactics for open-term reasoning) and the
   authoritative Java `TypeChecker`/`Reducer`. They must agree on what is well-typed; merging them
   is high-risk (the Clojure kernel handles open metavars + an attachable mutable lctx the Java
   kernel has no API for), so instead this turns the standing divergence risk into a TEST FAILURE:
   for a sample of Init declarations, both kernels must infer def-equal types."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm])
  (:import [ansatz.kernel TypeChecker Env Expr]))

(def ^:private init-medium-env
  "Lazily loaded init-medium environment (local — does NOT touch the global ansatz-env)."
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:private sample-names
  "Init declarations spanning every ConstantInfo kind — definitions, constructors, inductives,
   recursors, theorems — so the conformance check exercises delta/iota/whnf and isDefEq."
  ["Nat" "Nat.zero" "Nat.succ" "Nat.add" "Nat.mul" "Nat.rec" "Nat.pred"
   "List" "List.nil" "List.cons" "List.rec" "List.append"
   "Bool" "Bool.rec" "Eq" "Eq.refl" "Eq.rec" "Or" "And"
   "Nat.add_zero" "Nat.zero_add" "Nat.succ_add"])

(defn- infer-agree?
  "The Clojure kernel and the Java kernel infer DEF-EQUAL types for `e` — the core two-kernel
   conformance: both inferers (and their underlying whnf / isDefEq) agree on `e`'s type."
  [^Env e-env ^TypeChecker jtc ^Expr e]
  (let [cT (tc/infer-type (tc/mk-tc-state e-env) e)
        jT (.inferType jtc e)]
    (.isDefEq jtc cT jT)))

(deftest two-kernel-conformance
  (testing "Clojure tactic-kernel (tc/reduce) agrees with the Java TypeChecker on a sample of Init decls"
    (if-let [e-env @init-medium-env]
      (let [jtc (TypeChecker. e-env)
            checked (atom 0)]
        (doseq [n sample-names]
          (when-let [ci (env/lookup e-env (nm/from-string n))]
            (swap! checked inc)
            (is (infer-agree? e-env jtc (.type ci))
                (str "two-kernel divergence on the TYPE of " n))
            (when-let [v (.value ci)]
              (is (infer-agree? e-env jtc v)
                  (str "two-kernel divergence on the VALUE of " n)))))
        (is (<= 15 @checked) "expected most sample decls present in init-medium"))
      (println "SKIP two-kernel-conformance: test-data/init-medium.ndjson not found"))))
