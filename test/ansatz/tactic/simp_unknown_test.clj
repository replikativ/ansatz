(ns ansatz.tactic.simp-unknown-test
  "Lean pairs: test/lean/simp_unknown.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once (fn [t] (a/load-init!) (binding [a/*verbose* false] (t))))

(defn- proves [& args]
  (apply a/prove-theorem args)
  true)

(deftest unknown-simp-entries-are-elaboration-errors
  (doseq [tactic '[(simp [no-such-lemma]) (simp only [no-such-lemma])
                   (simp_all [no-such-lemma]) (simp_all only [no-such-lemma])
                   (dsimp [no-such-lemma]) (dsimp only [no-such-lemma])
                   (dsimp [no-such-lemma] at h) (dsimp only [no-such-lemma] at h)
                   (simp [no-such-lemma] at h) (simp only [no-such-lemma] at h)]]
    (let [ty (elab/elaborate (a/env) '(forall [h :- True] True))
          [ps _] (proof/start-proof (a/env) ty)
          ps (basic/intro ps "h")
          ex (try (a/run-tactic ps tactic) nil
                  (catch clojure.lang.ExceptionInfo ex ex))]
      (is (= :elab-error (some-> ex ex-cause ex-data :kind)) (str tactic))
      (is (re-find #"Unknown constant: no-such-lemma" (or (some-> ex .getMessage) "")) (str tactic)))))

(deftest known-irrelevant-lemma-remains-valid
  (is (true? (proves 'known-irrelevant-lemma '[n :- Nat] '(= n n)
                     '[(simp only [Nat.add_zero])]))))

(deftest on-demand-packing-lemmas-remain-valid
  (doseq [tactic '[(simp only [Nat.add_eq]) (simp only [Nat.le_eq])]]
    (is (true? (proves (gensym "packing_lemma") '[n :- Nat] '(= n n) [tactic])))))
