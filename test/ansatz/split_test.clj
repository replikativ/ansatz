(ns ansatz.split-test
  "Faithful port of Lean 4 `split` (Tactic/Split.lean): case-split on an
   ite/dite/cond/Bool.rec discriminant in the goal. Goals are built at the kernel
   level because the surface `cond`/`ite` keywords intercept a/theorem elaboration.
   Each proof is checked with the AUTHORITATIVE check-constant (env/verifies?)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.attrs :as attrs]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]))

(def ^:private full
  (delay (let [f "test-data/init.ndjson"]
           (when (.exists (java.io.File. f))
             (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-env [t]
  (when @full
    (reset! a/ansatz-env @full)
    (attrs/load-bundled-attrs!))
  (t))
(use-fixtures :once with-env)

(def ^:private L1 (lvl/succ lvl/zero))
(defn- nat [] (e/const' (name/from-string "Nat") []))
(defn- c' [s ls] (e/const' (name/from-string s) ls))

(defn- prove [goal tac]
  (let [[ps _] (proof/start-proof (a/env) goal)
        ps (tac ps)
        term (extract/extract ps)]
    [(proof/solved? ps) (env/verifies? (a/env) goal term)]))

(deftest split-cond-bool
  ;; ∀ (c : Bool) (x : Nat), cond Nat c x x = x   — needs split on the Bool c
  (when @full
    (let [condapp (e/app* (c' "cond" [L1]) (nat) (e/bvar 1) (e/bvar 0) (e/bvar 0))
          eqn (e/app* (c' "Eq" [L1]) (nat) condapp (e/bvar 0))
          goal (e/forall' "c" (c' "Bool" []) (e/forall' "x" (nat) eqn :default) :default)
          [solved verifies]
          (prove goal (fn [ps]
                        (-> ps (basic/intros ["c" "x"]) (basic/split-tac)
                            (basic/all-goals (fn [p] (simp/simp-all p []))))))]
      (is solved "cond split: all goals closed")
      (is verifies "cond split: proof term kernel-verifies (Bool.rec by-cases)"))))

(deftest split-ite-decidable
  ;; ∀ (a b x : Nat), ite Nat (a = b) (instDecidableEqNat a b) x x = x
  ;; needs byCasesDec on the Decidable (a = b)
  (when @full
    (let [eqab (e/app* (c' "Eq" [L1]) (nat) (e/bvar 2) (e/bvar 1))
          inst (e/app* (c' "instDecidableEqNat" []) (e/bvar 2) (e/bvar 1))
          iteapp (e/app* (c' "ite" [L1]) (nat) eqab inst (e/bvar 0) (e/bvar 0))
          eqn (e/app* (c' "Eq" [L1]) (nat) iteapp (e/bvar 0))
          goal (e/forall' "a" (nat)
                          (e/forall' "b" (nat)
                                     (e/forall' "x" (nat) eqn :default) :default) :default)
          [solved verifies]
          (prove goal (fn [ps]
                        (-> ps (basic/intros ["a" "b" "x"]) (basic/split-tac)
                            (basic/all-goals (fn [p] (simp/simp-all p []))))))]
      (is solved "ite split: all goals closed")
      (is verifies "ite split: proof term kernel-verifies (Decidable.casesOn byCasesDec)"))))
