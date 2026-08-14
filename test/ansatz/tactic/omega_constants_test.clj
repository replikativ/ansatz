(ns ansatz.tactic.omega-constants-test
  "Store-completeness check for the omega tactic.

   `ansatz.tactic.omega-proof` names every lemma it can emit — most of them in one
   table (`omega-names`), a few inline as `(name/from-string \"…\")`. A name that does
   not resolve in the environment is a silent capability hole: the proof term
   referencing it is built and then rejected — or, more often, the whole branch is
   swallowed by a `try` and omega merely reports that it could not derive a
   contradiction. Nothing else in the suite notices, because the affected goals are
   exactly the ones nobody has a passing test for.

   So: assert every referenced name against the DEFAULT bundled environment
   (init-medium, 2997 declarations), with an explicit allow-list of today's gaps."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.omega-proof]))

(def known-missing-from-bundled-init
  "Constants omega refers to that the bundled `init-medium` slice does not carry.
   Each one costs a real capability:

     Decidable.not_iff, iff_iff_and_or_not_and_not   ¬(P ↔ Q) / (P ↔ Q) facts
     Decidable.not_or_of_imp, not_imp                implication hypotheses/goals
     not_and_or                                      ¬(P ∧ Q) goals
     Int.lt_or_gt_of_ne                              Int ≠ goals and hypotheses
     Int.mul_ediv_self_le, Int.lt_mul_ediv_self_add  Int division bounds
     Int.emod_eq_zero_of_dvd, Int.emod_pos_of_not_dvd,
     Nat.emod_pos_of_not_dvd, Nat.mod_eq_zero_of_dvd,
     Nat.div_mul_cancel                              divisibility (`∣`) facts
     Lean.Omega.bmod_*, Lean.Omega.IntList.bmod,
     Lean.Omega.Coeffs.bmod_coeffs                   hard-equality (balanced mod)
                                                     elimination — the `6x+7y=5`
                                                     integrality corpus entries
     Int.ofNat.eq_def                                unused helper

   THIS LIST SHOULD SHRINK TO EMPTY as the exported store grows. It is not a
   specification of what omega needs, it is a record of what is missing; the test
   below prints the entries that have become removable."
  #{"Decidable.not_iff"
    "Decidable.not_or_of_imp"
    "Int.emod_eq_zero_of_dvd"
    "Int.emod_pos_of_not_dvd"
    "Int.lt_mul_ediv_self_add"
    "Int.lt_or_gt_of_ne"
    "Int.mul_ediv_self_le"
    "Int.ofNat.eq_def"
    "Lean.Omega.bmod_sat"
    "Lean.Omega.bmod_coeffs"
    "Lean.Omega.bmod_div_term"
    "Lean.Omega.IntList.bmod"
    "Lean.Omega.Coeffs.bmod_coeffs"
    "Nat.div_mul_cancel"
    "Nat.emod_pos_of_not_dvd"
    "Nat.mod_eq_zero_of_dvd"
    "iff_iff_and_or_not_and_not"
    "not_and_or"
    "not_imp"})

(defn- table-names
  "Constant names in `omega-proof`'s `omega-names` table."
  []
  (into #{} (map (comp name/->string val))
        @(ns-resolve 'ansatz.tactic.omega-proof 'omega-names)))

(defn- inline-names
  "Constant names spelled inline in omega_proof.clj as (name/from-string \"…\").
   Read from source: they are just as load-bearing as the table entries, and
   `Nat.div_mul_cancel` (the Nat divisibility fact) is only referenced that way."
  []
  (if-let [src (io/resource "ansatz/tactic/omega_proof.clj")]
    (into #{} (map second) (re-seq #"name/from-string \"([^\"]+)\"" (slurp src)))
    #{}))

(defn- referenced-names [] (into (table-names) (inline-names)))

(deftest omega-names-resolve-in-bundled-init
  (testing "every constant omega can emit resolves, modulo the documented allow-list"
    (let [e (or @test-env/init-medium-env
                (throw (ex-info "init-medium not found — cannot check omega's constants" {})))
          referenced (referenced-names)
          resolves? (fn [n] (some? (env/lookup e (name/from-string n))))
          missing (into (sorted-set) (remove resolves?) referenced)
          unexpected (remove known-missing-from-bundled-init missing)]
      (is (seq referenced) "found the constant references to check")
      (is (empty? unexpected)
          (str "omega references constants absent from the bundled init and not on "
               "the known-gap allow-list: " (str/join ", " unexpected)
               " — either the store lost a declaration, or a new lemma was referenced "
               "without checking that it is exported."))
      ;; Not a failure — a nudge. An allow-list entry is dead weight once the store
      ;; carries it, or once omega stops referencing it at all.
      (let [removable (sort (remove missing known-missing-from-bundled-init))]
        (when (seq removable)
          (println "  NOTE: known-missing-from-bundled-init entries that now resolve"
                   "(or are no longer referenced) — delete them:"
                   (str/join ", " removable)))
        (is true "allow-list staleness reported")))))

(deftest bool-bridge-and-minmax-constants-present
  (testing "the lemmas the Bool→Prop bridge and min/max splitting depend on are exported"
    (let [e (or @test-env/init-medium-env
                (throw (ex-info "init-medium not found" {})))]
      (doseq [n ["Nat.ble" "Nat.blt"
                 "Nat.le_of_ble_eq_true" "Nat.not_le_of_not_ble_eq_true"
                 "Bool.noConfusion"
                 "Min.min" "Max.max" "minOfLe" "maxOfLe"
                 "if_pos" "if_neg" "Decidable.em" "Or.elim" "Or.inl" "Or.inr"
                 "And.intro"]]
        (is (some? (env/lookup e (name/from-string n)))
            (str n " must be present — omega emits it unconditionally"))))))
