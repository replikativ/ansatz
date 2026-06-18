(ns ansatz.generalizing-test
  "Validate `(induction xs generalizing acc)` — the accumulator-generalizing induction the wandler
   foldl laws need. Proves the foldl init-extraction law thinly (the shape of
   wandler.laws.proofs.frame/prove-foldl-add-init), kernel-verified via check-constant."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private full
  (delay (let [f "test-data/init.ndjson"]
           (when (.exists (java.io.File. f))
             (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))
(defn- with-env [t] (when @full (reset! a/ansatz-env @full)) (t))
(use-fixtures :once with-env)

(defn- has? [s] (some? (env/lookup (a/env) (name/from-string s))))
(defn- verifies? [s]
  (let [ci (env/lookup (a/env) (name/from-string s))]
    (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))

(deftest generalizing-ih-consumed
  (when @full
    ;; Isolates the affordance: `induction xs generalizing acc` must produce the ∀-quantified IH
    ;; (∀ acc, …) AND simp_all must consume it. The const-step foldl closes purely on the IH —
    ;; cons reduces (via foldl_cons + β) to `foldl (λa _.a) acc tail = acc`, which is exactly the
    ;; IH at acc. No arithmetic / associativity (those associative-foldl laws need controlled `rw`,
    ;; as in Lean — a separate concern from this tactic).
    (a/theorem foldl_const_step [acc :- Nat, xs :- (List Nat)]
      (= Nat (List.foldl (fn [a :- Nat, x :- Nat] a) acc xs) acc)
      (induction xs generalizing acc)
      (all_goals (simp_all [List.foldl_nil List.foldl_cons])))
    (is (has? "foldl_const_step") "the const-step foldl law installed")
    (is (verifies? "foldl_const_step") "kernel-checks (check-constant, authoritative)")))
