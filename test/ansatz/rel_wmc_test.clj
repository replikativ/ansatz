;; Exact PROBABILITY-OF-PROVABILITY via the ProofsProb provenance: the search
;; tag records which uncertain facts each alternative proof uses (a DNF), and
;; `combined-measure` is the weighted model count — the probability the goal is
;; provable given the facts' credences, counting a SHARED fact once (unlike a
;; naive independent-OR of proof probabilities). This is the measurable object
;; standard Lean has no notion of (Tier 3).
(ns ansatz.rel-wmc-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.rel :as r]
            [ansatz.provenance :as prov]))

(defn- ≈ [a b] (< (Math/abs (- (double a) (double b))) 1e-9))

(deftest proofsprob-semiring-is-correlation-aware
  (testing "ProofsProb ⊗=∧, ⊕=∨, recover=WMC — a shared fact is counted once"
    (let [P prov/proofs-prov
          A (prov/prov-fact P :A 0.5)
          B (prov/prov-fact P :B 0.5)
          C (prov/prov-fact P :C 0.5)
          AB (prov/prov-times P A B)              ; proof 1 uses A ∧ B
          AC (prov/prov-times P A C)              ; proof 2 uses A ∧ C
          both (prov/prov-plus P AB AC)]          ; either proof: (A∧B) ∨ (A∧C)
      (is (≈ 1.0 (prov/prov-recover P (prov/prov-one P))) "⊤ = 1")
      (is (≈ 0.0 (prov/prov-recover P (prov/prov-zero P))) "⊥ = 0")
      (is (≈ 0.25 (prov/prov-recover P AB)) "P(A∧B) = 0.25")
      (is (≈ 0.375 (prov/prov-recover P both))
          "P((A∧B)∨(A∧C)) = P(A)·P(B∨C) = 0.5·0.75 — shared A counted ONCE")
      (is (≈ 0.4375 (- 1.0 (* 0.75 0.75)))
          "a naive independent-OR of the two 0.25 proofs would give 0.4375 ≠ 0.375"))))

(deftest probability-of-provability-over-the-search
  (testing "run a search with two proofs depending on overlapping uncertain
            facts; combined-measure is the exact probability-of-provability"
    (let [P prov/proofs-prov
          search (r/condw
                  [1 (r/facto :A 0.5 (fn [] (r/facto :B 0.5 (fn [] r/succeed))))]
                  [1 (r/facto :A 0.5 (fn [] (r/facto :C 0.5 (fn [] r/succeed))))])
          states (r/run 5 (r/state nil :prov P) search)]
      (is (= 2 (count states)) "two alternative proofs")
      (is (≈ 0.375 (r/combined-measure P states))
          "exact WMC over the proof space, correlation-aware")
      ;; a single proof's own measure is just its conjunction
      (is (≈ 0.25 (r/measure (first states))) "one proof = P(its facts)"))))

(deftest provenance-instances-are-swappable
  (testing "the SAME facto search reports different measures per semiring —
            the driver is measure-agnostic (Boolean=provable?, MaxMinProb=best)"
    (let [mk (fn [P] (r/run 5 (r/state nil :prov P)
                            (r/condw [1 (r/facto :A 0.5 (fn [] r/succeed))]
                                     [1 (r/facto :B 0.9 (fn [] r/succeed))])))]
      (is (true? (r/combined-measure prov/boolean-prov (mk prov/boolean-prov)))
          "Boolean: provable at all?")
      ;; MaxMinProb ⊕=max, and condw folds the NORMALIZED branch prior (0.5) as
      ;; part of the measure → best proof = 0.5 (proposal) × 0.9 (fact) = 0.45.
      (is (≈ 0.45 (r/combined-measure prov/maxminprob-prov (mk prov/maxminprob-prov)))
          "MaxMinProb: best proof, proposal-prior × fact-credence")
      ;; ProofsProb IGNORES proposal priors (from-prob→⊤) and tracks only the
      ;; labeled facts: P(A@0.5 ∨ B@0.9) = 1-(1-0.5)(1-0.9) = 0.95. The clean
      ;; fact-vs-proposal separation the measure decomposition prescribes.
      (is (≈ 0.95 (r/combined-measure prov/proofs-prov (mk prov/proofs-prov)))
          "ProofsProb: exact P(either proof's facts hold), facts only"))))
